import VbmSimd.Find
import VbmSimdProofs.Lanes
import VbmSimdProofs.Shims
/-! # Proof: the word-at-a-time search is the byte-at-a-time machine (`[VS-11]`) -/
namespace VbmSimdProofs
open VbmSimd

theorem bit_rep8 (b : UInt8) (k j : Nat) (hk : k < 8) (hj : j < 8) : bit (rep8 b) (8 * k + j) = b.toBitVec.getLsbD j := by
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  have hj8 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hj8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rep8, bit, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft]

theorem byte_of_bits (w : UInt64) (k : Nat) (v : BitVec 8) (h : ∀ j, j < 8 → bit w (8 * k + j) = v.getLsbD j) : byte w k = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [byte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  exact h j hj

theorem byte_ld64Model (a : ByteArray) (i k : Nat) (hk : k < 8) : byte (ld64Model a i) k = (byteAt0 a (i + k)).toBitVec :=
  byte_of_bits _ _ _ fun j hj => ld64Model_bit a i k j hk hj

theorem byte_rep8 (b : UInt8) (k : Nat) (hk : k < 8) : byte (rep8 b) k = b.toBitVec := byte_of_bits _ _ _ fun j hj => bit_rep8 b k j hk hj

/-- The flag of lane `k` of `eqSet` over the word at `i`: byte `i + k` is a member (zero past the end, as `ld64` reads it). -/
theorem dec_beq (x y : UInt8) : decide (x.toBitVec = y.toBitVec) = (x == y) := by
  rw [Bool.eq_iff_iff]; simp [UInt8.toBitVec_inj]

theorem eqSet_lane (a : ByteArray) (s : UInt32) (i k : Nat) (hk : k < 8) :
    bit (eqSet (rep8 s.toUInt8) (rep8 (s >>> 8).toUInt8) (rep8 (s >>> 16).toUInt8) (rep8 (s >>> 24).toUInt8) (ld64Model a i)) (8 * k + 7) = inSet s (byteAt0 a (i + k)) := by
  simp only [eqSet, bit_or, eqLanes_spec _ _ k hk, laneEq, byte_ld64Model a i k hk, byte_rep8 _ k hk, inSet, dec_beq]

theorem eqSet_low (c0 c1 c2 c3 w : UInt64) (p : Nat) (hp : p < 64) (h : p % 8 ≠ 7) : bit (eqSet c0 c1 c2 c3 w) p = false := by
  simp [eqSet, bit_or, eqLanes_low _ _ p hp h]

/-- A word whose only possible bits are lane tops: if it is not zero, `ctz m / 8` is the first flagged lane. -/
theorem first_lane (m : UInt64) (low : ∀ p, p < 64 → p % 8 ≠ 7 → bit m p = false) (hm : m ≠ 0) :
    ∃ l, l < 8 ∧ (ctz m >>> 3).toNat = l ∧ bit m (8 * l + 7) = true ∧ ∀ k, k < l → bit m (8 * k + 7) = false := by
  obtain ⟨h1, h2, h3⟩ := ctzModel_spec m hm
  have hc : (ctz m).toNat = (ctzModel m).toNat := rfl
  have h7 : (ctzModel m).toNat % 8 = 7 := by
    refine Classical.byContradiction fun hne => ?_
    have := low _ h1 hne
    rw [h2] at this; exact absurd this (by simp)
  refine ⟨(ctzModel m).toNat / 8, by omega, ?_, by rw [show 8 * ((ctzModel m).toNat / 8) + 7 = (ctzModel m).toNat by omega]; exact h2, fun k hk => h3 _ (by omega)⟩
  rw [UInt64.toNat_shiftRight, hc]
  simp [Nat.shiftRight_eq_div_pow]

theorem findSpec_end (a : ByteArray) (s : UInt32) (i : Nat) (h : a.size ≤ i) : findSpec a s i = a.size := by
  rw [findSpec]; simp [Nat.not_lt.mpr h]

theorem byteAt0_of_lt (a : ByteArray) (i : Nat) (h : i < a.size) : byteAt0 a i = a[i] := by
  simp [byteAt0, Array.getD_eq_getD_getElem?, h]
  rfl

theorem findSpec_hit (a : ByteArray) (s : UInt32) (i : Nat) (h : i < a.size) (hs : inSet s (byteAt0 a i) = true) : findSpec a s i = i := by
  rw [byteAt0_of_lt a i h] at hs; rw [findSpec]; simp [h, hs]

theorem findSpec_miss (a : ByteArray) (s : UInt32) (i : Nat) (h : i < a.size) (hs : inSet s (byteAt0 a i) = false) : findSpec a s i = findSpec a s (i + 1) := by
  rw [byteAt0_of_lt a i h] at hs
  rw [findSpec]; simp [h, hs]

/-- `d` bytes from `i` that are not members (the ones that exist) can be skipped. -/
theorem findSpec_run (a : ByteArray) (s : UInt32) : ∀ d i, (∀ k, k < d → i + k < a.size → inSet s (byteAt0 a (i + k)) = false) → findSpec a s i = findSpec a s (i + d) := by
  intro d
  induction d with
  | zero => intro i _; rfl
  | succ d ih =>
    intro i h
    by_cases hi : i < a.size
    · rw [findSpec_miss a s i hi (by simpa using h 0 (by omega) (by omega)), ih (i + 1) (fun k hk hk2 => by
        have := h (k + 1) (by omega) (by omega); rwa [show i + (k + 1) = i + 1 + k by omega] at this)]
      rw [show i + 1 + d = i + (d + 1) by omega]
    · rw [findSpec_end a s i (by omega), findSpec_end a s (i + (d + 1)) (by omega)]

theorem usize8 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide : 8 < 2 ^ 32) USize.le_size)

/-- `[VS-11]` the loop is the machine, from any `i` below the end. -/
theorem findSwarGo_spec (a : ByteArray) (s : UInt32) (n : USize) (hn : n.toNat = a.size) :
    ∀ f (i : USize), n.toNat - i.toNat ≤ f → i < n →
      (findSwarGo a n (rep8 s.toUInt8) (rep8 (s >>> 8).toUInt8) (rep8 (s >>> 16).toUInt8) (rep8 (s >>> 24).toUInt8) i).toNat = findSpec a s i.toNat := by
  intro f
  induction f with
  | zero => intro i hf hi; have := USize.lt_iff_toNat_lt.mp hi; omega
  | succ f ih =>
    intro i hf hi
    have hI := USize.lt_iff_toNat_lt.mp hi
    have hN := USize.toNat_lt_size n
    have hsub : (n - i).toNat = n.toNat - i.toNat := USize.toNat_sub_of_le n i (USize.le_iff_toNat_le.mpr (by omega))
    have hld : ld64 a i = ld64Model a i.toNat := rfl
    have hlane := eqSet_lane a s i.toNat
    have hlow := eqSet_low (rep8 s.toUInt8) (rep8 (s >>> 8).toUInt8) (rep8 (s >>> 16).toUInt8) (rep8 (s >>> 24).toUInt8) (ld64Model a i.toNat)
    rw [findSwarGo]; simp only [hi, ↓reduceDIte]
    generalize hm : eqSet (rep8 s.toUInt8) (rep8 (s >>> 8).toUInt8) (rep8 (s >>> 16).toUInt8) (rep8 (s >>> 24).toUInt8) (ld64 a i) = m
    rw [hld] at hm
    rw [hm] at hlane hlow
    by_cases hm0 : m = 0
    · subst hm0
      have hrun := findSpec_run a s 8 i.toNat (fun k hk _ => by rw [← hlane k hk]; simp [bit])
      have h8 := usize8
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hc : 8 < n - i
      · have hc' := USize.lt_iff_toNat_lt.mp hc
        have hi8 : i + 8 < n := by
          rw [USize.lt_iff_toNat_lt, USize.toNat_add, h8, ← show USize.size = 2 ^ System.Platform.numBits from rfl, Nat.mod_eq_of_lt (by omega)]; omega
        simp only [hc, ↓reduceIte]
        rw [ih (i + 8) (by rw [USize.toNat_add, h8, ← show USize.size = 2 ^ System.Platform.numBits from rfl, Nat.mod_eq_of_lt (by omega)]; omega) hi8, hrun,
          USize.toNat_add, h8, ← show USize.size = 2 ^ System.Platform.numBits from rfl, Nat.mod_eq_of_lt (by omega)]
      · have hc' : ¬ 8 < (n - i).toNat := fun h => hc (USize.lt_iff_toNat_lt.mpr (by rw [h8]; exact h))
        simp only [hc, ↓reduceIte]
        rw [hrun, findSpec_end a s _ (by omega), hn]
    · obtain ⟨l, hl8, hl, hbit, hlt⟩ := first_lane m hlow hm0
      have hl' : ((ctz m >>> 3).toUSize).toNat = l := by rw [UInt64.toNat_toUSize, ← hl]; exact Nat.mod_eq_of_lt (by have := USize.le_size; have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := this; omega)
      have hrun := fun d => findSpec_run a s d i.toNat
      simp only [bne_iff_ne, ne_eq, hm0, not_false_eq_true, ↓reduceIte]
      by_cases hc : (ctz m >>> 3).toUSize < n - i
      · have hc' : l < n.toNat - i.toNat := by have := USize.lt_iff_toNat_lt.mp hc; omega
        simp only [hc, ↓reduceIte]
        rw [USize.toNat_add, hl', ← show USize.size = 2 ^ System.Platform.numBits from rfl, Nat.mod_eq_of_lt (by omega),
          hrun l (fun k hk _ => by rw [← hlane k (by omega), hlt k hk]), findSpec_hit a s _ (by omega) (by rw [← hlane l hl8, hbit])]
      · have hc' : ¬ l < n.toNat - i.toNat := fun h => hc (USize.lt_iff_toNat_lt.mpr (by rw [hl', hsub]; exact h))
        simp only [hc, ↓reduceIte]
        rw [hrun (n.toNat - i.toNat) (fun k hk _ => by rw [← hlane k (by omega), hlt k (by omega)]), findSpec_end a s _ (by omega), hn]

/-- `[VS-11]` the portable word-at-a-time search is the byte-at-a-time machine: for every array, set and start. -/
theorem findSwar_spec (a : ByteArray) (s : UInt32) (i : Nat) : findSwar a s i = findSpec a s i := by
  unfold findSwar
  by_cases hn : a.usize.toNat = a.size
  · simp only [hn, ↓reduceDIte]
    by_cases hi : i < a.size
    · simp only [hi, ↓reduceIte]
      have hN := USize.toNat_lt_size a.usize
      have hi' : i.toUSize.toNat = i := by rw [USize.toNat_ofNat', ← show USize.size = 2 ^ System.Platform.numBits from rfl]; exact Nat.mod_eq_of_lt (by omega)
      have := findSwarGo_spec a s a.usize hn _ i.toUSize (Nat.le_refl _) (USize.lt_iff_toNat_lt.mpr (by omega))
      rw [this, hi']
    · simp only [hi, ↓reduceIte]
      rw [findSpec_end a s i (by omega)]
  · simp only [hn, ↓reduceDIte]

/-- The result of the machine is at most the size when the start is below it. -/
theorem findSpec_le (a : ByteArray) (s : UInt32) : ∀ f i, a.size - i ≤ f → findSpec a s i ≤ a.size := by
  intro f
  induction f with
  | zero => intro i h; rw [findSpec_end a s i (by omega)]; exact Nat.le_refl _
  | succ f ih =>
    intro i h
    by_cases hi : i < a.size
    · by_cases hs : inSet s (byteAt0 a i) = true
      · rw [findSpec_hit a s i hi hs]; omega
      · rw [findSpec_miss a s i hi (by simpa using hs)]; exact ih (i + 1) (by omega)
    · rw [findSpec_end a s i (by omega)]; exact Nat.le_refl _

/-- `[VS-11]` the AVX2 path (by its model) is the machine. -/
theorem findAvx_spec (a : ByteArray) (s : UInt32) (i : Nat) : findAvx a s i = findSpec a s i := by
  unfold findAvx
  by_cases h : i < a.size ∧ a.usize.toNat = a.size
  · simp only [h, and_self, ↓reduceIte]
    have hN := USize.toNat_lt_size a.usize
    have hi : i.toUSize.toNat = i := by rw [USize.toNat_ofNat', ← show USize.size = 2 ^ System.Platform.numBits from rfl]; exact Nat.mod_eq_of_lt (by omega)
    have hle := findSpec_le a s _ i (Nat.le_refl _)
    show (USize.ofNat (findSpec a s i.toUSize.toNat)).toNat = _
    rw [hi, USize.toNat_ofNat', ← show USize.size = 2 ^ System.Platform.numBits from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [h, ↓reduceIte]

/-- `[VS-11]` the search a consumer calls is the machine, whatever the CPU test says. -/
theorem findFirstOf_spec (a : ByteArray) (s : UInt32) (i : Nat) : findFirstOf a s i = findSpec a s i := by
  unfold findFirstOf
  split
  · exact findAvx_spec a s i
  · exact findSwar_spec a s i

end VbmSimdProofs
