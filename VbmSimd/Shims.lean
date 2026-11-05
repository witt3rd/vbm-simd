import VbmSimd.Spec
/-! # `VbmSimd.Shims`: the four trusted primitives, and their Lean models

Lean's C emitter turns eight byte loads and shifts into eight loads and shifts (clang does not combine them into one 8-byte load), and re-checks that an array is exclusive before every byte store. Four
tiny C functions (`include/vbm_simd.h`, `static inline` so the compiler sees through them) fix that: an 8-byte load, an 8-byte store, a 4-byte store, and a count of trailing zero bits. Measured on a prototype
of a 64-byte classifier: about 350 MB/s as emitted, about 880 MB/s with the first two (the rest of the gap to a vector unit is arithmetic).

Every function here is `@[extern]` with a **Lean body that is its specification** (the *model*): the proofs use the model, the compiled code runs the C, and `tests/ShimTest.lean` (Tier 1) runs the C
against the model on boundary and random cases. Both are **total**: an index past the end of the array reads as zero bytes (`ld64`), or writes nothing past the end (`st64`, `st32`), exactly as the
model says, so no call can touch memory outside the array and no precondition is left for the caller to prove. A shim decides nothing; it moves and counts bits. Trust ledger entry T10.

A consumer compiles its generated C with `-include include/vbm_simd.h` (the header is included first, before the `extern` declarations Lean emits). -/
namespace VbmSimd

/-- Byte `n` of `a`, `0` past the end (the model of an out-of-range read). -/
def byteAt0 (a : ByteArray) (n : Nat) : UInt8 := a.data.getD n 0

/-- `[VS-5]` MODEL of `vbm_simd_ld64`: the little-endian `u64` of the eight bytes at offset `i`; bytes past the end of `a` read as zero. -/
def ld64Model (a : ByteArray) (i : Nat) : UInt64 :=
  (byteAt0 a i).toUInt64 ||| ((byteAt0 a (i + 1)).toUInt64 <<< 8) ||| ((byteAt0 a (i + 2)).toUInt64 <<< 16) ||| ((byteAt0 a (i + 3)).toUInt64 <<< 24) |||
  ((byteAt0 a (i + 4)).toUInt64 <<< 32) ||| ((byteAt0 a (i + 5)).toUInt64 <<< 40) ||| ((byteAt0 a (i + 6)).toUInt64 <<< 48) ||| ((byteAt0 a (i + 7)).toUInt64 <<< 56)

/-- MODEL of `vbm_simd_st64`: `a` with the eight bytes of `w`, little-endian, stored at byte offset `8 * k`; a byte that would fall past the end is not stored. -/
def st64Model (a : ByteArray) (k : Nat) (w : UInt64) : ByteArray :=
  let i := 8 * k
  ((((((((a.set! i w.toUInt8).set! (i + 1) (w >>> 8).toUInt8).set! (i + 2) (w >>> 16).toUInt8).set! (i + 3) (w >>> 24).toUInt8).set! (i + 4) (w >>> 32).toUInt8).set! (i + 5) (w >>> 40).toUInt8).set! (i + 6) (w >>> 48).toUInt8).set! (i + 7) (w >>> 56).toUInt8)

/-- MODEL of `vbm_simd_st32`: the four bytes of `w`, little-endian, stored at byte offset `4 * k`; a byte past the end is not stored. -/
def st32Model (a : ByteArray) (k : Nat) (w : UInt32) : ByteArray :=
  let i := 4 * k
  ((((a.set! i w.toUInt8).set! (i + 1) (w >>> 8).toUInt8).set! (i + 2) (w >>> 16).toUInt8).set! (i + 3) (w >>> 24).toUInt8)

/-- The first position at or after `i` (and below `i + f`) whose bit is set; `64` when there is none (`f` is the fuel). -/
def ctzFrom (x : UInt64) : Nat → Nat → Nat
  | 0, _ => 64
  | f + 1, i => if bit x i then i else ctzFrom x f (i + 1)

/-- `[VS-6]` MODEL of `vbm_simd_ctz`: the number of trailing zero bits of `x`, `64` for `x = 0` (`ctzModel_spec`). -/
def ctzModel (x : UInt64) : UInt64 := UInt64.ofNat (ctzFrom x 64 0)

/-- One 8-byte little-endian load at byte offset `i` (model: `ld64Model`). `a` is borrowed. -/
@[extern "vbm_simd_ld64"] def ld64 (a : @& ByteArray) (i : USize) : UInt64 := ld64Model a i.toNat

/-- One 8-byte little-endian store at word index `k` (byte offset `8k`), in place when `a` is not shared (model: `st64Model`). -/
@[extern "vbm_simd_st64"] def st64 (a : ByteArray) (k : USize) (w : UInt64) : ByteArray := st64Model a k.toNat w

/-- One 4-byte little-endian store at index `k` (byte offset `4k`), in place when `a` is not shared (model: `st32Model`). -/
@[extern "vbm_simd_st32"] def st32 (a : ByteArray) (k : USize) (w : UInt32) : ByteArray := st32Model a k.toNat w

/-- The count of trailing zero bits (model: `ctzModel`); `tzcnt`/`ctz` on hardware. -/
@[extern "vbm_simd_ctz"] def ctz (x : UInt64) : UInt64 := ctzModel x

end VbmSimd
