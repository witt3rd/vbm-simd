import VbmSimd.Spec
/-! # Bit-level lemmas shared by the proofs: `bit` of the `UInt64` operations. -/
namespace VbmSimdProofs
open VbmSimd

theorem bit_and (x y : UInt64) (i : Nat) : bit (x &&& y) i = (bit x i && bit y i) := by simp [bit]
theorem bit_or (x y : UInt64) (i : Nat) : bit (x ||| y) i = (bit x i || bit y i) := by simp [bit]
theorem bit_xor (x y : UInt64) (i : Nat) : bit (x ^^^ y) i = (bit x i ^^ bit y i) := by simp [bit]
theorem bit_not (x : UInt64) (i : Nat) (hi : i < 64) : bit (~~~x) i = !bit x i := by simp [bit, hi]
theorem bit_ge (x : UInt64) (i : Nat) (hi : 64 ≤ i) : bit x i = false := by simp [bit, BitVec.getLsbD_of_ge, hi]

/-- Two words with the same bits are equal. -/
theorem ext_bits (x y : UInt64) (h : ∀ i, i < 64 → bit x i = bit y i) : x = y := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h i hi

end VbmSimdProofs
