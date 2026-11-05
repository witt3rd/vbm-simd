import VbmSimd.Shims
import VbmSimdProofs.Bits
/-! # Proofs about the shim models: what a load reads (`[VS-5]`) and what `ctz` counts (`[VS-6]`)

The C shims are tested against these models (`tests/ShimTest.lean`); these theorems say what the models mean, so that proofs about kernels that call `ld64` and `ctz` can use the
meaning (byte `j` of the loaded word is byte `i + j` of the array; `ctz x` is the position of the lowest set bit) without looking at the model's body. -/
namespace VbmSimdProofs
open VbmSimd

/-- `[VS-5]` bit `b` of byte `j` of the word `ld64Model a i` is bit `b` of byte `i + j` of `a` (zero past the end). -/
theorem ld64Model_bit (a : ByteArray) (i j b : Nat) (hj : j < 8) (hb : b < 8) :
    bit (ld64Model a i) (8 * j + b) = (byteAt0 a (i + j)).toBitVec.getLsbD b := by
  have hj8 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  have hb8 : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases hj8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ld64Model, bit]

theorem ctzFrom_spec (x : UInt64) : ∀ f i, i + f = 64 →
    i ≤ ctzFrom x f i ∧ ctzFrom x f i ≤ 64 ∧ (ctzFrom x f i < 64 → bit x (ctzFrom x f i) = true ∧ ∀ j, i ≤ j → j < ctzFrom x f i → bit x j = false) ∧
      (ctzFrom x f i = 64 → ∀ j, i ≤ j → j < 64 → bit x j = false) := by
  intro f
  induction f with
  | zero => intro i h; simp only [ctzFrom]; refine ⟨by omega, by omega, fun h => by omega, fun _ j h1 h2 => by omega⟩
  | succ f ih =>
    intro i h
    by_cases hb : bit x i = true
    · have e : ctzFrom x (f + 1) i = i := by simp [ctzFrom, hb]
      rw [e]
      exact ⟨Nat.le_refl _, by omega, fun _ => ⟨hb, fun j hij hj => by omega⟩, fun h64 => by omega⟩
    · have hb' : bit x i = false := by simpa using hb
      obtain ⟨h1, h1', h2, h3⟩ := ih (i + 1) (by omega)
      simp only [ctzFrom, hb', Bool.false_eq_true, ite_false]
      refine ⟨by omega, h1', fun hlt => ?_, fun h64 j hij hj => ?_⟩
      · obtain ⟨a, b⟩ := h2 hlt
        refine ⟨a, fun j hij hj => ?_⟩
        by_cases hji : j = i
        · subst hji; exact hb'
        · exact b j (by omega) hj
      · by_cases hji : j = i
        · subst hji; exact hb'
        · exact h3 h64 j (by omega) hj

/-- `[VS-6]` for `x ≠ 0`, `ctz x` is below 64, bit `ctz x` of `x` is set and every lower bit is clear. -/
theorem ctzModel_spec (x : UInt64) (hx : x ≠ 0) :
    (ctzModel x).toNat < 64 ∧ bit x (ctzModel x).toNat = true ∧ ∀ j, j < (ctzModel x).toNat → bit x j = false := by
  obtain ⟨h1, h1', h2, h3⟩ := ctzFrom_spec x 64 0 rfl
  have hlt : ctzFrom x 64 0 < 64 := by
    refine Classical.byContradiction fun hge => ?_
    have h64 : ctzFrom x 64 0 = 64 := by omega
    apply hx
    apply ext_bits
    intro i hi
    have := h3 h64 i (by omega) hi
    rw [this]; simp [bit]
  have e : (ctzModel x).toNat = ctzFrom x 64 0 := by
    simp only [ctzModel, UInt64.toNat_ofNat']; omega
  rw [e]
  obtain ⟨a, b⟩ := h2 hlt
  exact ⟨hlt, a, fun j hj => b j (by omega) hj⟩

/-- `[VS-6]` `ctz 0 = 64`. -/
theorem ctzModel_zero : ctzModel 0 = 64 := by
  have h : ctzFrom 0 64 0 = 64 := by
    obtain ⟨h1, h1', h2, h3⟩ := ctzFrom_spec 0 64 0 rfl
    refine Classical.byContradiction fun hne => ?_
    have hlt : ctzFrom 0 64 0 < 64 := by omega
    have := (h2 hlt).1
    simp [bit] at this
  simp [ctzModel, h]

end VbmSimdProofs
