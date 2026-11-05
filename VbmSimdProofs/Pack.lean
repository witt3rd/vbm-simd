import VbmSimd.Lanes
import VbmSimdProofs.Bits
/-! # Proof: `pack8` packs the eight lane flags (`[VS-4]`)

The input has only lane flags (every bit that is not the top bit of its lane is zero), so it is determined by eight Booleans (`flags_eq`). For the 256 combinations the claim is checked by `decide`
(`pack8_flags`): the multiply-and-shift of `pack8` is evaluated on `flagsWord b0 .. b7` and must equal the flags in the low byte. The multiply is a product of partial products that sit at distinct bit
positions, so there are no carries; `decide` checks exactly that, for every flag pattern, without any argument about carries. -/
namespace VbmSimdProofs
open VbmSimd

/-- the flag of lane `s / 8` set or clear: bit `s` of the word, for `s < 64`. -/
def fl (b : Bool) (s : Nat) : UInt64 := if b then (1 : UInt64) <<< UInt64.ofNat s else 0

theorem bit_fl (b : Bool) (s i : Nat) (hs : s < 64) : bit (fl b s) i = (b && decide (i = s)) := by
  cases b
  · simp [fl, bit]
  · have e : ((1 : UInt64) <<< UInt64.ofNat s).toBitVec = 1#64 <<< s := by
      simp [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_ofNat, Nat.mod_eq_of_lt hs]
    simp only [fl, ite_true, bit, e, BitVec.getLsbD_shiftLeft, Bool.true_and]
    by_cases h : i < 64
    · by_cases hsi : s ≤ i
      · by_cases hh : i = s
        · subst hh; simp [h]
        · have : 1 ≤ i - s := by omega
          have h0 : (1#64).getLsbD (i - s) = false := by
            simp only [BitVec.getLsbD, BitVec.toNat_ofNat]
            exact Nat.testBit_lt_two_pow (by simpa using Nat.one_lt_two_pow (show i - s ≠ 0 by omega))
          simp [h, hh, h0]
      · simp [h, hsi, show i ≠ s by omega]
    · simp [h, show i ≠ s by omega]

def flagsWord (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : UInt64 := fl b0 7 ||| fl b1 15 ||| fl b2 23 ||| fl b3 31 ||| fl b4 39 ||| fl b5 47 ||| fl b6 55 ||| fl b7 63
def lowByte (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : UInt64 := fl b0 0 ||| fl b1 1 ||| fl b2 2 ||| fl b3 3 ||| fl b4 4 ||| fl b5 5 ||| fl b6 6 ||| fl b7 7

theorem pack8_flags : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, pack8 (flagsWord b0 b1 b2 b3 b4 b5 b6 b7) = lowByte b0 b1 b2 b3 b4 b5 b6 b7 := by decide

/-- a word with only lane flags is its flags. -/
theorem flags_eq (m : UInt64) (hm : ∀ i, i < 64 → i % 8 ≠ 7 → bit m i = false) :
    m = flagsWord (bit m 7) (bit m 15) (bit m 23) (bit m 31) (bit m 39) (bit m 47) (bit m 55) (bit m 63) := by
  apply ext_bits
  intro i hi
  simp only [flagsWord, bit_or, bit_fl _ _ _ (show 7 < 64 by omega), bit_fl _ _ _ (show 15 < 64 by omega), bit_fl _ _ _ (show 23 < 64 by omega),
    bit_fl _ _ _ (show 31 < 64 by omega), bit_fl _ _ _ (show 39 < 64 by omega), bit_fl _ _ _ (show 47 < 64 by omega),
    bit_fl _ _ _ (show 55 < 64 by omega), bit_fl _ _ _ (show 63 < 64 by omega)]
  by_cases h7 : i % 8 = 7
  · have : i = 7 ∨ i = 15 ∨ i = 23 ∨ i = 31 ∨ i = 39 ∨ i = 47 ∨ i = 55 ∨ i = 63 := by omega
    rcases this with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · rw [hm i hi h7]
    have : i ≠ 7 ∧ i ≠ 15 ∧ i ≠ 23 ∧ i ≠ 31 ∧ i ≠ 39 ∧ i ≠ 47 ∧ i ≠ 55 ∧ i ≠ 63 := by omega
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := this
    simp [a1, a2, a3, a4, a5, a6, a7, a8]

/-- `[VS-4]` bit `k` of `pack8 m` is the flag of lane `k` (for a mask with only lane flags). -/
theorem pack8_spec (m : UInt64) (hm : ∀ i, i < 64 → i % 8 ≠ 7 → bit m i = false) (k : Nat) (hk : k < 8) : bit (pack8 m) k = laneFlag m k := by
  have h := pack8_flags (bit m 7) (bit m 15) (bit m 23) (bit m 31) (bit m 39) (bit m 47) (bit m 55) (bit m 63)
  rw [← flags_eq m hm] at h
  rw [h]
  simp only [lowByte, bit_or, bit_fl _ _ _ (show 0 < 64 by omega), bit_fl _ _ _ (show 1 < 64 by omega), bit_fl _ _ _ (show 2 < 64 by omega), bit_fl _ _ _ (show 3 < 64 by omega),
    bit_fl _ _ _ (show 4 < 64 by omega), bit_fl _ _ _ (show 5 < 64 by omega), bit_fl _ _ _ (show 6 < 64 by omega), bit_fl _ _ _ (show 7 < 64 by omega), laneFlag]
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk8 with h | h | h | h | h | h | h | h <;> subst h <;> simp

/-- `[VS-4]` nothing is set above the low eight bits of `pack8 m`. -/
theorem pack8_high (m : UInt64) (hm : ∀ i, i < 64 → i % 8 ≠ 7 → bit m i = false) (i : Nat) (hi : 8 ≤ i) : bit (pack8 m) i = false := by
  have h := pack8_flags (bit m 7) (bit m 15) (bit m 23) (bit m 31) (bit m 39) (bit m 47) (bit m 55) (bit m 63)
  rw [← flags_eq m hm] at h
  rw [h]
  simp only [lowByte, bit_or, bit_fl _ _ _ (show 0 < 64 by omega), bit_fl _ _ _ (show 1 < 64 by omega), bit_fl _ _ _ (show 2 < 64 by omega), bit_fl _ _ _ (show 3 < 64 by omega),
    bit_fl _ _ _ (show 4 < 64 by omega), bit_fl _ _ _ (show 5 < 64 by omega), bit_fl _ _ _ (show 6 < 64 by omega), bit_fl _ _ _ (show 7 < 64 by omega)]
  have : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 4 ∧ i ≠ 5 ∧ i ≠ 6 ∧ i ≠ 7 := by omega
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := this
  simp [a1, a2, a3, a4, a5, a6, a7, a8]

end VbmSimdProofs
