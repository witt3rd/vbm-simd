import VbmSimd.Inset
/-! # `VbmSimd.Classify`: the class masks of 64 bytes by nibble tables (the AVX2 classifier, `[VS-14]`)

`classify64 a i t ms out` computes, for the block of 64 bytes at `i`, four masks at once and stores them as the words 0 to 3 of `out`. A byte `v` has the class bits `classByte t v`: the byte `v & 15` of the table `t` (its first 16
bytes) and the byte `v >> 4` of the second 16 bytes, and-ed (the nibble tables of a vector classifier: two byte shuffles per 32 bytes of input). Mask `r` (the byte `r` of `ms`) flags the byte `i + p` iff it exists and its class
bits meet that mask byte. One call replaces a call of `inset64` per mask (each re-reads the block and re-broadcasts its constants); the tables and the masks are the caller's, so what a class *is* stays in Lean: the shim moves and
tests bits (`include/vbm_simd.h`, trust ledger T14). The Lean body is the model: the per-byte machine `classSpec` for each mask, stored with `stFull` (a word is stored only where all eight of its bytes lie inside `out`). A consumer
calls it only where `hasAvx2 () || hasNeon ()` (the shim's body is the AVX2 one or, on aarch64, the NEON one of T15 there; the scalar loop elsewhere is correct but slow) and runs its own proved portable kernel otherwise. -/
namespace VbmSimd

/-- The class bits of byte `v` under the nibble tables `t` (bytes 0 to 15: by low nibble; 16 to 31: by high nibble; zero past the end of `t`). -/
def classByte (t : ByteArray) (v : UInt8) : UInt8 := byteAt0 t (v &&& 15).toNat &&& byteAt0 t (16 + (v >>> 4).toNat)

/-- `[VS-14]` the class mask machine: bit `p` of the mask for the block at `i` is set iff byte `i + p` exists and its class bits meet the mask byte `m`; bytes at or past the end give `0`. -/
def classSpec (a : ByteArray) (i : Nat) (t : ByteArray) (m : UInt8) : UInt64 :=
  maskFrom (fun p => decide (i + p < a.size) && ((classByte t (byteAt0 a (i + p)) &&& m) != 0)) 64

/-- The eight bytes of `w` stored at word `k` only when all of them lie inside `a` (nothing is stored otherwise). -/
def stFull (a : ByteArray) (k : Nat) (w : UInt64) : ByteArray := if 8 * k + 8 ≤ a.size then st64Model a k w else a

/-- The model of `classify64`: the four masks of the block at `i`, for the mask bytes of `ms` (byte 0 first), stored as words 0 to 3 of `out` where they fit. -/
def classifyModel (a : ByteArray) (i : Nat) (t : ByteArray) (ms : UInt32) (out : ByteArray) : ByteArray :=
  stFull (stFull (stFull (stFull out 0 (classSpec a i t ms.toUInt8)) 1 (classSpec a i t (ms >>> 8).toUInt8)) 2 (classSpec a i t (ms >>> 16).toUInt8)) 3 (classSpec a i t (ms >>> 24).toUInt8)

/-- The four class masks of the 64 bytes at `i` (the mask bytes are the four bytes of `ms`) as words 0 to 3 of `out`, in place when `out` is not shared (model: `classifyModel`). `a` and `t` are borrowed. -/
@[extern "vbm_simd_classify64"] def classify64 (a : @& ByteArray) (i : USize) (t : @& ByteArray) (ms : UInt32) (out : ByteArray) : ByteArray := classifyModel a i.toNat t ms out

end VbmSimd
