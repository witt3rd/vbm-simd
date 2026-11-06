import VbmSimd.Inset
import VbmSimdProofs.Bits
/-! # Proof: the membership mask is the byte-at-a-time machine (`[VS-12]`)

`insetSpec` is the machine itself (`maskFrom` of the per-byte predicate); what is proved here is what a consumer uses: bit `p` of the mask of the block at `i` is "byte `i + p` exists and is in the set", for every `p < 64`. -/
namespace VbmSimdProofs
open VbmSimd

theorem bit_one_shl (n p : Nat) (hn : n < 64) : bit ((1 : UInt64) <<< n.toUInt64) p = decide (p = n) := by
  have h1 : (n.toUInt64.toBitVec % 64).toNat = n := by
    simp [Nat.toUInt64, BitVec.toNat_umod]
    omega
  unfold bit
  rw [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', h1]
  simp only [BitVec.getLsbD_shiftLeft, UInt64.toBitVec_one, BitVec.getLsbD_one]
  by_cases h : p = n
  · subst h; simp [hn]
  · by_cases h2 : p < n
    · simp [h2, h]
    · have : p - n ≠ 0 := by omega
      simp [h2, h, this]

theorem bit_maskFrom (f : Nat → Bool) : ∀ n, n ≤ 64 → ∀ p, bit (maskFrom f n) p = (decide (p < n) && f p) := by
  intro n
  induction n with
  | zero => intro _ p; simp [maskFrom, bit]
  | succ n ih =>
    intro hn p
    simp only [maskFrom, bit_or]
    rw [ih (by omega) p]
    by_cases hf : f n = true
    · simp only [hf, ↓reduceIte, bit_one_shl n p (by omega)]
      by_cases hp : p = n
      · subst hp; simp [hf]
      · simp only [hp, decide_false, Bool.or_false]
        by_cases hlt : p < n
        · simp [hlt, show p < n + 1 by omega]
        · simp [hlt, show ¬ p < n + 1 by omega]
    · simp only [hf, Bool.false_eq_true, ↓reduceIte]
      have : bit (0 : UInt64) p = false := by simp [bit]
      rw [this, Bool.or_false]
      by_cases hp : p = n
      · subst hp; simp [hf]
      · by_cases hlt : p < n
        · simp [hlt, show p < n + 1 by omega]
        · simp [hlt, show ¬ p < n + 1 by omega]

/-- `[VS-12]` bit `p` of the membership mask of the block at `i` is set iff byte `i + p` exists and is in the set. -/
theorem bit_insetSpec (a : ByteArray) (i : Nat) (s : UInt32) (p : Nat) (hp : p < 64) :
    bit (insetSpec a i s) p = (decide (i + p < a.size) && inSet s (byteAt0 a (i + p))) := by
  unfold insetSpec
  rw [bit_maskFrom _ 64 (Nat.le_refl _) p]
  simp [hp]

/-- `[VS-12]` the AVX2 call is the machine (by its model: the C body is tested against it, `tests/ShimTest.lean`). -/
theorem inset64_spec (a : ByteArray) (i : USize) (s : UInt32) : inset64 a i s = insetSpec a i.toNat s := rfl

end VbmSimdProofs
