import VbmSimd.Lanes
import VbmSimd.Shims
/-! # `VbmSimd.Find`: the first byte of an array that is in a small set (portable, eight bytes per step)

`findSwar a s i` is the index of the first byte at or after `i` that is one of the (at most four) bytes of `s`, or the size of `a` when there is none: the question a line splitter asks (the first LF or CR),
a delimiter scanner (the first of `,` `"` `\n`) or a tokenizer. The machine is `findSpec` (`[VS-11]`); the kernel loads eight bytes (`ld64`, zero past the end), flags the lanes equal to a member
(`eqLanes`, four of them, or-ed) and takes the first flagged lane with `ctz`. The padding zeros of a last partial word can flag a lane past the end; the result is clamped to the size, which is exact
because a real match comes first. Proved: `VbmSimdProofs.Find` (`findSwar_spec`): standard axioms only, no `bv_decide`. Everything here is plain Lean (no C beyond the `ld64` and `ctz` shims). -/
namespace VbmSimd

/-- A byte repeated in all eight lanes (computed once per search, before the loop: a closed term is not folded, see `Lanes`). -/
@[inline] def rep8 (b : UInt8) : UInt64 := let x := b.toUInt64; let x := x ||| (x <<< 8); let x := x ||| (x <<< 16); x ||| (x <<< 32)

/-- `0x80` in each lane of `w` that equals the byte repeated in `c0`, `c1`, `c2` or `c3`. -/
@[inline] def eqSet (c0 c1 c2 c3 w : UInt64) : UInt64 := eqLanes c0 w ||| eqLanes c1 w ||| eqLanes c2 w ||| eqLanes c3 w

/-- The loop: `n` is the size of the array and `i < n`; `c0 .. c3` are the members repeated in all lanes. The first flagged lane `l` of the word at `i` gives `i + l` if that is below `n` (else `n`);
with no flag the loop goes on eight bytes, or ends at `n` when the word reached the end. -/
def findSwarGo (a : ByteArray) (n : USize) (c0 c1 c2 c3 : UInt64) (i : USize) : USize :=
  if h : i < n then
    let m := eqSet c0 c1 c2 c3 (ld64 a i)
    if m != 0 then (let l := (ctz m >>> 3).toUSize; if l < n - i then i + l else n)
    else if 8 < n - i then findSwarGo a n c0 c1 c2 c3 (i + 8) else n
  else n
termination_by n.toNat - i.toNat
decreasing_by
  have h1 := USize.lt_iff_toNat_lt.mp h
  have h2 := USize.lt_iff_toNat_lt.mp ‹8 < n - i›
  have h3 := USize.toNat_sub_of_le n i (USize.le_iff_toNat_le.mpr (by omega))
  have h4 := USize.toNat_lt_size n
  have h5 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide : 8 < 2 ^ 32) USize.le_size)
  have h6 : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_add, h5, ← h6, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The first byte at or after `i` that is a member of `s`, by words, when the size of the array is a word (it always is); `n` otherwise `a.size`. `findSwar_spec`: it is `findSpec`. -/
def findSwar (a : ByteArray) (s : UInt32) (i : Nat) : Nat :=
  let n := a.usize
  if _hn : n.toNat = a.size then
    (if i < a.size then (findSwarGo a n (rep8 s.toUInt8) (rep8 (s >>> 8).toUInt8) (rep8 (s >>> 16).toUInt8) (rep8 (s >>> 24).toUInt8) i.toUSize).toNat else a.size)
  else findSpec a s i

/-! ## The AVX2 and NEON searches, and the choice between them and `findSwar`

`vbm_simd_find_avx2` (`include/vbm_simd.h`, trust ledger T11) is the C body of `findAvx2`, whose Lean body `findSpec` is its model; it is tested against that model and against `findSwar`
(`tests/ShimTest.lean`). `hasAvx2 ()` asks the CPU once (cpuid, and that the OS saves the vector state). `vbm_simd_find_neon` (trust ledger T15) is the NEON twin, with the same model; `hasNeon ()` is a compile-time fact (aarch64). `findFirstOf` takes the AVX2 shim when the CPU has it, the NEON shim on aarch64, and the proved `findSwar` otherwise;
`findFirstOf_spec` holds for either answer of the CPU test, so the proof does not depend on which one a machine gives. -/

/-- Does this CPU (and OS) run AVX2? The model says `false`; `findFirstOf_spec` is true for either value. `never_extract`: the compiler must not hoist `hasAvx2 ()` into a closed constant computed once at start-up (`lean_uint8_once`, a runtime function the freestanding builds of the consumers do not have); the shim caches the answer itself. -/
@[extern "vbm_simd_has_avx2", never_extract] def hasAvx2 (_ : Unit) : Bool := false

/-- The AVX2 search, 32 bytes per step, never reading outside the array (model: `findSpec`; the index is a word and the result is `a.size` when there is no match or `i` is past the end). -/
@[extern "vbm_simd_find_avx2"] def findAvx2 (a : @& ByteArray) (s : UInt32) (i : USize) : USize := (findSpec a s i.toNat).toUSize

/-- Does this build run NEON (aarch64, compiled by clang)? A compile-time fact of the shim: NEON is part of the aarch64 base architecture, so there is no CPU test. The model says `false`; `findFirstOf_spec` is true for either value. `never_extract` as `hasAvx2`. -/
@[extern "vbm_simd_has_neon", never_extract] def hasNeon (_ : Unit) : Bool := false

/-- The NEON search, 32 bytes per step, never reading outside the array (model: `findSpec`, as `findAvx2`). `vbm_simd_find_neon`, trust ledger T15; the scalar loop on a build without NEON. -/
@[extern "vbm_simd_find_neon"] def findNeon (a : @& ByteArray) (s : UInt32) (i : USize) : USize := (findSpec a s i.toNat).toUSize

/-- `findAvx2` for a start that is a `Nat` (the machine itself when the size or the start does not fit a word). -/
def findAvx (a : ByteArray) (s : UInt32) (i : Nat) : Nat :=
  if i < a.size ∧ a.usize.toNat = a.size then (findAvx2 a s i.toUSize).toNat else findSpec a s i

/-- `findNeon` for a start that is a `Nat` (as `findAvx`). -/
def findNeonN (a : ByteArray) (s : UInt32) (i : Nat) : Nat :=
  if i < a.size ∧ a.usize.toNat = a.size then (findNeon a s i.toUSize).toNat else findSpec a s i

/-- `[VS-11]` The first byte at or after `i` that is a member of `s` (`a.size` when there is none): the AVX2 search on a CPU that has it, the NEON search on aarch64, the proved portable search otherwise. -/
def findFirstOf (a : ByteArray) (s : UInt32) (i : Nat) : Nat :=
  if hasAvx2 () then findAvx a s i else if hasNeon () then findNeonN a s i else findSwar a s i

end VbmSimd
