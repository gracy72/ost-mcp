//! Node database layer: header, page framing, the node and block BTrees, and
//! block payload assembly.
//!
//! Everything variant-specific lives in [`Geom`]. Entry records (BTENTRY,
//! NBTENTRY, BBTENTRY) are identical across both supported versions, so only the
//! page envelope is parameterised.

use crate::{Error, Result};
use memmap2::Mmap;
use std::collections::HashMap;
use std::fs::File;
use std::path::Path;

pub(crate) fn u16le(b: &[u8], o: usize) -> u16 {
    u16::from_le_bytes([b[o], b[o + 1]])
}

pub(crate) fn u32le(b: &[u8], o: usize) -> u32 {
    u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]])
}

pub(crate) fn u64le(b: &[u8], o: usize) -> u64 {
    let mut a = [0u8; 8];
    a.copy_from_slice(&b[o..o + 8]);
    u64::from_le_bytes(a)
}

/// BID bit 0 is reserved and must be ignored when comparing (MS-PST 2.2.2.2).
fn bid_key(bid: u64) -> u64 {
    bid & !1
}

/// BID bit 1 marks an internal block: an XBLOCK/XXBLOCK data tree or an
/// SLBLOCK/SIBLOCK subnode tree rather than leaf data.
fn bid_is_internal(bid: u64) -> bool {
    bid & 0x02 != 0
}

/// Page framing, the only thing that differs between the supported versions.
#[derive(Clone, Copy, Debug)]
pub struct Geom {
    /// Page size in bytes.
    pub page: usize,
    /// Offset of the BTPAGE header (`cEnt`) within a page.
    pub bt_hdr: usize,
    /// v36 widened `cEnt`/`cEntMax` from u8 to u16, which shifts the two fields
    /// that follow them.
    pub counts_u16: bool,
    /// First bit of `hidBlockIndex` in a HID. MS-PST puts it at 16, giving an
    /// 11-bit `hidIndex`; v36 moves it to 19, giving 14 bits. Determined
    /// empirically: on a v36 heap of 304 blocks, `hidUserRoot` 0x03484520 only
    /// resolves to a valid TCINFO under the bit-19 split.
    pub hid_block_shift: u32,
}

impl Geom {
    fn cb_ent_off(self) -> usize {
        if self.counts_u16 {
            4
        } else {
            2
        }
    }

    fn c_level_off(self) -> usize {
        if self.counts_u16 {
            5
        } else {
            3
        }
    }
}

/// One NBT leaf entry: a node and the blocks holding its data and subnodes.
#[derive(Clone, Copy, Debug)]
pub struct Node {
    pub nid: u32,
    pub bid_data: u64,
    pub bid_sub: u64,
    pub nid_parent: u32,
}

/// One BBT leaf entry: where a block lives and how many bytes are stored.
#[derive(Clone, Copy, Debug)]
pub struct BlockRef {
    pub ib: u64,
    /// Stored size. For a compressed block this is the *compressed* length.
    pub cb: u16,
    pub cref: u16,
}

pub struct Pff {
    map: Mmap,
    pub ver: u16,
    pub geom: Geom,
    /// `bCryptMethod` from the header: 0 = none, 1 = PERMUTE.
    crypt: u8,
    pub nbt: HashMap<u32, Node>,
    pub bbt: HashMap<u64, BlockRef>,
}

impl Pff {
    pub fn open(path: impl AsRef<Path>) -> Result<Pff> {
        // Rust opens with share mode READ|WRITE|DELETE on Windows, so this
        // succeeds against a running Outlook; the mapping then bypasses the
        // byte-range lock Outlook holds on the header.
        let file = File::open(path.as_ref())?;
        let map = unsafe { Mmap::map(&file)? };
        Self::from_map(map)
    }

    fn from_map(map: Mmap) -> Result<Pff> {
        if map.len() < 0x210 {
            return Err(Error::Format("file shorter than a PFF header".into()));
        }
        if &map[0..4] != b"!BDN" {
            return Err(Error::Format("missing !BDN magic".into()));
        }
        // 'SM' is a PST, 'SO' an OST. MS-PST documents only the former.
        let client = u16le(&map, 8);
        if client != 0x4D53 && client != 0x4F53 {
            return Err(Error::Format(format!(
                "unexpected wMagicClient 0x{client:04X}"
            )));
        }
        let ver = u16le(&map, 10);
        let geom = match ver {
            23 => Geom {
                page: 512,
                bt_hdr: 488,
                counts_u16: false,
                hid_block_shift: 16,
            },
            36 => Geom {
                page: 4096,
                bt_hdr: 4056,
                counts_u16: true,
                hid_block_shift: 19,
            },
            14 | 15 => {
                return Err(Error::Unsupported(
                    "32-bit ANSI PFF (wVer 14/15, Outlook 2002 and earlier)".into(),
                ))
            }
            v => return Err(Error::Unsupported(format!("unknown PFF wVer {v}"))),
        };
        // NDB_CRYPT_PERMUTE (1) and NDB_CRYPT_CYCLIC (2) need the 512-byte
        // substitution table from MS-PST 5.1, which is not implemented yet.
        // Rejecting here keeps every block read below unconditional.
        let crypt = map[0x201];
        if crypt > 1 {
            return Err(Error::Unsupported(format!(
                "bCryptMethod {crypt} (NDB_CRYPT_CYCLIC) needs the header key, which is not implemented"
            )));
        }

        let nbt_ib = u64le(&map, 0xE0);
        let bbt_ib = u64le(&map, 0xF0);
        let mut pff = Pff {
            map,
            ver,
            geom,
            crypt,
            nbt: HashMap::new(),
            bbt: HashMap::new(),
        };

        let mut bbt = HashMap::new();
        pff.walk_leaves(bbt_ib, &mut |pg, c_ent, cb_ent| {
            for i in 0..c_ent {
                let o = i * cb_ent;
                bbt.insert(
                    bid_key(u64le(pg, o)),
                    BlockRef {
                        ib: u64le(pg, o + 8),
                        cb: u16le(pg, o + 16),
                        cref: u16le(pg, o + 18),
                    },
                );
            }
        })?;
        pff.bbt = bbt;

        let mut nbt = HashMap::new();
        pff.walk_leaves(nbt_ib, &mut |pg, c_ent, cb_ent| {
            for i in 0..c_ent {
                let o = i * cb_ent;
                // The NID is 4 bytes, widened to 8 in Unicode files to match
                // the width of BTENTRY.btkey.
                let nid = u64le(pg, o) as u32;
                nbt.insert(
                    nid,
                    Node {
                        nid,
                        bid_data: u64le(pg, o + 8),
                        bid_sub: u64le(pg, o + 16),
                        nid_parent: u32le(pg, o + 24),
                    },
                );
            }
        })?;
        pff.nbt = nbt;

        Ok(pff)
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn page(&self, ib: u64) -> Result<&[u8]> {
        let s = ib as usize;
        let e = s
            .checked_add(self.geom.page)
            .ok_or_else(|| Error::Format("page offset overflow".into()))?;
        self.map
            .get(s..e)
            .ok_or_else(|| Error::Format(format!("page at 0x{ib:X} is past EOF")))
    }

    /// Visit every leaf page of a BTree. The callback receives the page bytes,
    /// the live entry count, and the entry stride.
    fn walk_leaves(&self, root_ib: u64, f: &mut dyn FnMut(&[u8], usize, usize)) -> Result<()> {
        let g = self.geom;
        let mut stack = vec![(root_ib, 0usize)];
        while let Some((ib, depth)) = stack.pop() {
            if depth > 16 {
                return Err(Error::Format("BTree deeper than 16 levels".into()));
            }
            let pg = self.page(ib)?;
            let c_ent = if g.counts_u16 {
                u16le(pg, g.bt_hdr) as usize
            } else {
                pg[g.bt_hdr] as usize
            };
            let cb_ent = pg[g.bt_hdr + g.cb_ent_off()] as usize;
            let c_level = pg[g.bt_hdr + g.c_level_off()];
            if cb_ent == 0 || c_ent.saturating_mul(cb_ent) > g.bt_hdr {
                return Err(Error::Format(format!(
                    "BTree page at 0x{ib:X} claims {c_ent} entries of {cb_ent} bytes"
                )));
            }
            if c_level == 0 {
                f(pg, c_ent, cb_ent);
                continue;
            }
            // BTENTRY: btkey u64, BREF { bid u64, ib u64 }
            for i in 0..c_ent {
                stack.push((u64le(pg, i * cb_ent + 16), depth + 1));
            }
        }
        Ok(())
    }

    pub fn node(&self, nid: u32) -> Result<Node> {
        self.nbt
            .get(&nid)
            .copied()
            .ok_or_else(|| Error::NotFound(format!("nid 0x{nid:X} is not in the node BTree")))
    }

    /// One block's payload, inflated if the file stored it compressed.
    ///
    /// v36 stores most block payloads as raw zlib streams. There is no flag for
    /// it anywhere in the BBTENTRY (`dwPadding` was tested and ruled out across
    /// 200k blocks), so detection is a header sniff plus a successful inflate.
    fn block(&self, bid: u64) -> Result<Vec<u8>> {
        let e = *self
            .bbt
            .get(&bid_key(bid))
            .ok_or_else(|| Error::NotFound(format!("bid 0x{bid:X} is not in the block BTree")))?;
        let s = e.ib as usize;
        let end = s
            .checked_add(e.cb as usize)
            .ok_or_else(|| Error::Format("block offset overflow".into()))?;
        let raw = self
            .map
            .get(s..end)
            .ok_or_else(|| Error::Format(format!("block 0x{bid:X} is past EOF")))?;
        // NDB_CRYPT_PERMUTE ("compressible encryption", what Outlook writes
        // by default for PSTs) is a fixed byte substitution over the payload:
        // no key material, no length change. Decrypting here keeps the zlib
        // sniff below applicable to the plaintext bytes.
        // Only leaf payloads carry the substitution. Measured on a v23 PST:
        // the SLBLOCK at bid 0xD0097A still began with its btype byte 0x02 in
        // clear, while the leaf heap of the same folder decrypted to a valid
        // HNHDR (bSig 0xEC, bClientSig 0x7C). Decrypting an internal block that
        // already starts with a block type would turn 0x02 into 0xB4 and stop
        // the subnode tree dead.
        let looks_like_block = matches!(raw.first(), Some(0x01) | Some(0x02));
        let raw: std::borrow::Cow<'_, [u8]> = if self.crypt == 1
            && (!bid_is_internal(bid) || !looks_like_block)
        {
            std::borrow::Cow::Owned(raw.iter().map(|b| PERMUTE[*b as usize]).collect())
        } else {
            std::borrow::Cow::Borrowed(raw)
        };
        if looks_zlib(&raw) {
            if let Some(v) = inflate(&raw) {
                return Ok(v);
            }
        }
        Ok(raw.into_owned())
    }

    /// Assemble a node's data tree into its constituent blocks, in order. A leaf
    /// bid yields one block; an internal bid is an XBLOCK or XXBLOCK whose
    /// children are concatenated.
    pub fn data_blocks(&self, bid: u64) -> Result<Vec<Vec<u8>>> {
        self.data_blocks_at(bid, 0)
    }

    fn data_blocks_at(&self, bid: u64, depth: usize) -> Result<Vec<Vec<u8>>> {
        let payload = self.block(bid)?;
        if !bid_is_internal(bid) {
            return Ok(vec![payload]);
        }
        if depth > 4 {
            return Err(Error::Format("data tree deeper than 4 levels".into()));
        }
        if payload.len() < 8 {
            return Err(Error::Format(format!("XBLOCK 0x{bid:X} is truncated")));
        }
        if payload[0] != 0x01 {
            return Err(Error::Format(format!(
                "bid 0x{bid:X} is internal but btype is 0x{:02X}, expected 0x01",
                payload[0]
            )));
        }
        let c_ent = u16le(&payload, 2) as usize;
        if 8 + c_ent * 8 > payload.len() {
            return Err(Error::Format(format!(
                "XBLOCK 0x{bid:X} claims {c_ent} children but holds {} bytes",
                payload.len()
            )));
        }
        // An XXBLOCK's children are XBLOCK bids, which carry the internal flag
        // themselves, so one recursion handles both levels.
        let mut out = Vec::new();
        for i in 0..c_ent {
            out.extend(self.data_blocks_at(u64le(&payload, 8 + i * 8), depth + 1)?);
        }
        Ok(out)
    }

    pub fn data_flat(&self, bid: u64) -> Result<Vec<u8>> {
        Ok(self.data_blocks(bid)?.concat())
    }

    /// A node's subnode BTree, flattened to `nid -> (bid_data, bid_sub)`.
    pub fn subnodes(&self, bid_sub: u64) -> Result<HashMap<u32, (u64, u64)>> {
        let mut out = HashMap::new();
        if bid_sub != 0 {
            self.subnodes_into(bid_sub, &mut out, 0)?;
        }
        Ok(out)
    }

    fn subnodes_into(
        &self,
        bid: u64,
        out: &mut HashMap<u32, (u64, u64)>,
        depth: usize,
    ) -> Result<()> {
        if depth > 4 {
            return Err(Error::Format("subnode tree deeper than 4 levels".into()));
        }
        let payload = self.block(bid)?;
        if payload.len() < 8 {
            return Err(Error::Format(format!("SLBLOCK 0x{bid:X} is truncated")));
        }
        if payload[0] != 0x02 {
            return Err(Error::Format(format!(
                "subnode block 0x{bid:X} btype is 0x{:02X}, expected 0x02",
                payload[0]
            )));
        }
        let c_level = payload[1];
        let c_ent = u16le(&payload, 2) as usize;
        let stride = if c_level == 0 { 24 } else { 16 };
        if 8 + c_ent * stride > payload.len() {
            return Err(Error::Format(format!(
                "subnode block 0x{bid:X} claims {c_ent} entries but holds {} bytes",
                payload.len()
            )));
        }
        for i in 0..c_ent {
            let o = 8 + i * stride;
            if c_level == 0 {
                // SLENTRY: nid u64, bidData u64, bidSub u64
                out.insert(
                    u64le(&payload, o) as u32,
                    (u64le(&payload, o + 8), u64le(&payload, o + 16)),
                );
            } else {
                // SIENTRY: nid u64, bid u64
                self.subnodes_into(u64le(&payload, o + 8), out, depth + 1)?;
            }
        }
        Ok(())
    }
}

/// MS-PST 5.1 compressible encryption table (`bCryptMethod` 1).
///
/// The same 256 values as libpst's `comp_enc` and libpff's
/// `libpff_encryption_compressible`. Encryption and decryption are the same
/// operation: every payload byte is replaced by `PERMUTE[byte]`.
static PERMUTE: [u8; 256] = [
    0x47, 0xf1, 0xb4, 0xe6, 0x0b, 0x6a, 0x72, 0x48, 0x85, 0x4e, 0x9e, 0xeb, 0xe2, 0xf8, 0x94, 0x53,
    0xe0, 0xbb, 0xa0, 0x02, 0xe8, 0x5a, 0x09, 0xab, 0xdb, 0xe3, 0xba, 0xc6, 0x7c, 0xc3, 0x10, 0xdd,
    0x39, 0x05, 0x96, 0x30, 0xf5, 0x37, 0x60, 0x82, 0x8c, 0xc9, 0x13, 0x4a, 0x6b, 0x1d, 0xf3, 0xfb,
    0x8f, 0x26, 0x97, 0xca, 0x91, 0x17, 0x01, 0xc4, 0x32, 0x2d, 0x6e, 0x31, 0x95, 0xff, 0xd9, 0x23,
    0xd1, 0x00, 0x5e, 0x79, 0xdc, 0x44, 0x3b, 0x1a, 0x28, 0xc5, 0x61, 0x57, 0x20, 0x90, 0x3d, 0x83,
    0xb9, 0x43, 0xbe, 0x67, 0xd2, 0x46, 0x42, 0x76, 0xc0, 0x6d, 0x5b, 0x7e, 0xb2, 0x0f, 0x16, 0x29,
    0x3c, 0xa9, 0x03, 0x54, 0x0d, 0xda, 0x5d, 0xdf, 0xf6, 0xb7, 0xc7, 0x62, 0xcd, 0x8d, 0x06, 0xd3,
    0x69, 0x5c, 0x86, 0xd6, 0x14, 0xf7, 0xa5, 0x66, 0x75, 0xac, 0xb1, 0xe9, 0x45, 0x21, 0x70, 0x0c,
    0x87, 0x9f, 0x74, 0xa4, 0x22, 0x4c, 0x6f, 0xbf, 0x1f, 0x56, 0xaa, 0x2e, 0xb3, 0x78, 0x33, 0x50,
    0xb0, 0xa3, 0x92, 0xbc, 0xcf, 0x19, 0x1c, 0xa7, 0x63, 0xcb, 0x1e, 0x4d, 0x3e, 0x4b, 0x1b, 0x9b,
    0x4f, 0xe7, 0xf0, 0xee, 0xad, 0x3a, 0xb5, 0x59, 0x04, 0xea, 0x40, 0x55, 0x25, 0x51, 0xe5, 0x7a,
    0x89, 0x38, 0x68, 0x52, 0x7b, 0xfc, 0x27, 0xae, 0xd7, 0xbd, 0xfa, 0x07, 0xf4, 0xcc, 0x8e, 0x5f,
    0xef, 0x35, 0x9c, 0x84, 0x2b, 0x15, 0xd5, 0x77, 0x34, 0x49, 0xb6, 0x12, 0x0a, 0x7f, 0x71, 0x88,
    0xfd, 0x9d, 0x18, 0x41, 0x7d, 0x93, 0xd8, 0x58, 0x2c, 0xce, 0xfe, 0x24, 0xaf, 0xde, 0xb8, 0x36,
    0xc8, 0xa1, 0x80, 0xa6, 0x99, 0x98, 0xa8, 0x2f, 0x0e, 0x81, 0x65, 0x73, 0xe4, 0xc2, 0xa2, 0x8a,
    0xd4, 0xe1, 0x11, 0xd0, 0x08, 0x8b, 0x2a, 0xf2, 0xed, 0x9a, 0x64, 0x3f, 0xc1, 0x6c, 0xf9, 0xec,
];

/// Sniff a zlib stream: low nibble of byte 0 is 8 (deflate) and the two header
/// bytes form a multiple of 31 (RFC 1950 check bits).
fn looks_zlib(b: &[u8]) -> bool {
    b.len() >= 2 && b[0] & 0x0F == 8 && (((b[0] as u16) << 8) | b[1] as u16).is_multiple_of(31)
}

fn inflate(b: &[u8]) -> Option<Vec<u8>> {
    use std::io::Read;
    let mut out = Vec::new();
    let mut d = flate2::read::ZlibDecoder::new(b);
    match d.read_to_end(&mut out) {
        Ok(_) if !out.is_empty() => Some(out),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zlib_sniff_accepts_real_headers_and_rejects_text() {
        assert!(looks_zlib(&[0x78, 0x9C]));
        assert!(looks_zlib(&[0x78, 0x01]));
        assert!(looks_zlib(&[0x78, 0xDA]));
        // An HNHDR never opens with a valid zlib header pair.
        assert!(!looks_zlib(&[0x0C, 0xEC]));
        assert!(!looks_zlib(&[0x3C, 0x68]));
        assert!(!looks_zlib(&[0x78]));
    }

    #[test]
    fn permute_table_is_a_bijection() {
        // A substitution table that is not a permutation would lose bytes.
        let mut seen = [false; 256];
        for v in PERMUTE {
            assert!(!seen[v as usize], "duplicate entry {v:#04x}");
            seen[v as usize] = true;
        }
    }

    #[test]
    fn bid_flags() {
        assert_eq!(bid_key(0x1D6E5DD), 0x1D6E5DC);
        assert!(bid_is_internal(0x02));
        assert!(!bid_is_internal(0x01));
    }
}
