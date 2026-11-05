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

/-! ## What the stores do -/

theorem size_set (a : ByteArray) (i : Nat) (v : UInt8) : (a.set! i v).size = a.size := by
  show (a.data.set! i v).size = a.data.size
  exact Array.size_set! _ _ _

theorem byteAt0_set (a : ByteArray) (i : Nat) (v : UInt8) (n : Nat) :
    byteAt0 (a.set! i v) n = if n = i ∧ i < a.size then v else byteAt0 a n := by
  unfold byteAt0
  show (a.data.set! i v).getD n 0 = _
  rw [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.getD_eq_getD_getElem?]
  have hs : a.size = a.data.size := rfl
  by_cases h1 : i = n
  · subst h1
    by_cases h2 : i < a.data.size
    · have h3 : i < a.size := h2
      simp only [h2, h3, ↓reduceIte, and_self, Option.getD_some]
    · have h3 : ¬ i < a.size := h2
      simp only [h2, h3, ↓reduceIte, and_false, Option.getD_none]
      rw [Array.getElem?_eq_none (by omega)]; rfl
  · have h3 : ¬ n = i := fun h => h1 h.symm
    simp only [h1, h3, ↓reduceIte, false_and]

/-- `[VS-5]` a 64-bit store keeps the size of the array. -/
theorem st64Model_size (a : ByteArray) (k : Nat) (w : UInt64) : (st64Model a k w).size = a.size := by
  simp only [st64Model, size_set]

/-- `[VS-5]` a 64-bit store leaves every byte outside the eight it writes as it was. -/
theorem byteAt0_st64Model_out (a : ByteArray) (k : Nat) (w : UInt64) (n : Nat) (h : n < 8 * k ∨ 8 * k + 8 ≤ n) : byteAt0 (st64Model a k w) n = byteAt0 a n := by
  have n0 : n ≠ 8 * k := by omega
  have n1 : n ≠ 8 * k + 1 := by omega
  have n2 : n ≠ 8 * k + 2 := by omega
  have n3 : n ≠ 8 * k + 3 := by omega
  have n4 : n ≠ 8 * k + 4 := by omega
  have n5 : n ≠ 8 * k + 5 := by omega
  have n6 : n ≠ 8 * k + 6 := by omega
  have n7 : n ≠ 8 * k + 7 := by omega
  simp [st64Model, byteAt0_set, n0, n1, n2, n3, n4, n5, n6, n7]

/-- `[VS-5]` a 64-bit store at word `k`, into an array with room for it, writes byte `j` of `w` at byte `8k + j`. -/
theorem byteAt0_st64Model_in (a : ByteArray) (k : Nat) (w : UInt64) (j : Nat) (hj : j < 8) (hk : 8 * k + 8 ≤ a.size) :
    byteAt0 (st64Model a k w) (8 * k + j) = (w >>> UInt64.ofNat (8 * j)).toUInt8 := by
  have h0 : 8 * k < a.size := by omega
  have h1 : 8 * k + 1 < a.size := by omega
  have h2 : 8 * k + 2 < a.size := by omega
  have h3 : 8 * k + 3 < a.size := by omega
  have h4 : 8 * k + 4 < a.size := by omega
  have h5 : 8 * k + 5 < a.size := by omega
  have h6 : 8 * k + 6 < a.size := by omega
  have h7 : 8 * k + 7 < a.size := by omega
  have hj8 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hj8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [st64Model, byteAt0_set, h0, h1, h2, h3, h4, h5, h6, h7]

theorem bit_byte_shr (w : UInt64) (j b : Nat) (hj : j < 8) (hb : b < 8) :
    ((w >>> UInt64.ofNat (8 * j)).toUInt8).toBitVec.getLsbD b = bit w (8 * j + b) := by
  have e : (w >>> UInt64.ofNat (8 * j)).toBitVec = w.toBitVec >>> (8 * j) := by
    simp [UInt64.toBitVec_shiftRight, Nat.mod_eq_of_lt (show 8 * j < 64 by omega)]
  simp only [UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, e, BitVec.getLsbD_ushiftRight, bit]

/-- `[VS-5]` a load of the word just stored returns it (the array has room for the store). -/
theorem ld64Model_st64Model_self (a : ByteArray) (k : Nat) (w : UInt64) (hk : 8 * k + 8 ≤ a.size) : ld64Model (st64Model a k w) (8 * k) = w := by
  apply ext_bits
  intro i hi
  have hi' : i = 8 * (i / 8) + i % 8 := by omega
  rw [hi', ld64Model_bit _ _ _ _ (by omega) (by omega), byteAt0_st64Model_in a k w (i / 8) (by omega) hk, bit_byte_shr _ _ _ (by omega) (by omega)]

/-- `[VS-5]` a store at word `k` does not change the load of any other word. -/
theorem ld64Model_st64Model_other (a : ByteArray) (k : Nat) (w : UInt64) (j : Nat) (hjk : j ≠ k) : ld64Model (st64Model a k w) (8 * j) = ld64Model a (8 * j) := by
  apply ext_bits
  intro i hi
  have hi' : i = 8 * (i / 8) + i % 8 := by omega
  rw [hi', ld64Model_bit _ _ _ _ (by omega) (by omega), ld64Model_bit _ _ _ _ (by omega) (by omega),
    byteAt0_st64Model_out a k w (8 * j + i / 8) (by omega)]

end VbmSimdProofs
