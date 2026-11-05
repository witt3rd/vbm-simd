import VbmSimdProofs.Lanes
import VbmSimdProofs.Pack
/-! # Proof: assembling the 64-bit mask of a block (`[VS-8]`)

`mask8 f w0 .. w7` is `f w0 ||| (f w1 <<< 8) ||| ...`: each word's eight bits go to their own byte of the mask. If `f` only ever sets the low eight bits, bit `8k + j` of the result is bit `j` of `f wk`: the
other seven terms contribute a zero there (a shift past it, or a byte that is not theirs). `eqMask64` is `mask8` of `pack8 (eqLanes c w)`, so its bit `p` says whether byte `p` of the block equals byte `p % 8` of `c`. -/
namespace VbmSimdProofs
open VbmSimd

/-- `x <<< s` for a literal shift: bit `i` is bit `i - s` of `x` for `s ≤ i < 64`. -/
theorem bit_shl (x : UInt64) (s : Nat) (hs : s < 64) (i : Nat) (hi : i < 64) : bit (x <<< (UInt64.ofNat s)) i = (decide (s ≤ i) && bit x (i - s)) := by
  have e : (x <<< UInt64.ofNat s).toBitVec = x.toBitVec <<< s := by
    simp [UInt64.toBitVec_shiftLeft, Nat.mod_eq_of_lt hs]
  simp only [bit, e, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  by_cases h : s ≤ i
  · simp [h, show ¬ i < s by omega]
  · simp [h, show i < s by omega]

/-- `[VS-8]` bit `8k + j` of `mask8 f w0 .. w7` is bit `j` of `f wk`, when `f` sets only low-byte bits. -/
theorem mask8_bit (f : UInt64 → UInt64) (hf : ∀ w i, 8 ≤ i → bit (f w) i = false) (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) (k j : Nat) (hk : k < 8) (hj : j < 8) :
    bit (mask8 f w0 w1 w2 w3 w4 w5 w6 w7) (8 * k + j) = bit (f (blockWord w0 w1 w2 w3 w4 w5 w6 w7 k)) j := by
  have hi : 8 * k + j < 64 := by omega
  have s8 : (8 : UInt64) = UInt64.ofNat 8 := rfl
  have s16 : (16 : UInt64) = UInt64.ofNat 16 := rfl
  have s24 : (24 : UInt64) = UInt64.ofNat 24 := rfl
  have s32 : (32 : UInt64) = UInt64.ofNat 32 := rfl
  have s40 : (40 : UInt64) = UInt64.ofNat 40 := rfl
  have s48 : (48 : UInt64) = UInt64.ofNat 48 := rfl
  have s56 : (56 : UInt64) = UInt64.ofNat 56 := rfl
  simp only [mask8, bit_or, s8, s16, s24, s32, s40, s48, s56, bit_shl _ _ (show 8 < 64 by omega) _ hi, bit_shl _ _ (show 16 < 64 by omega) _ hi,
    bit_shl _ _ (show 24 < 64 by omega) _ hi, bit_shl _ _ (show 32 < 64 by omega) _ hi, bit_shl _ _ (show 40 < 64 by omega) _ hi,
    bit_shl _ _ (show 48 < 64 by omega) _ hi, bit_shl _ _ (show 56 < 64 by omega) _ hi]
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  have hj8 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hj8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hf, blockWord]

/-- `[VS-8]` bit `8k + j` of `eqMask64 c w0 .. w7` says whether byte `j` of word `k` equals byte `j` of `c` (with `c` a byte repeated in all lanes: whether it is that byte). -/
theorem eqMask64_spec (c w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) (k j : Nat) (hk : k < 8) (hj : j < 8) :
    bit (eqMask64 c w0 w1 w2 w3 w4 w5 w6 w7) (8 * k + j) =
      laneEq c (blockWord w0 w1 w2 w3 w4 w5 w6 w7 k) j := by
  have hf : ∀ w i, 8 ≤ i → bit (pack8 (eqLanes c w)) i = false := fun w i hi => pack8_high _ (fun i' hi' h => eqLanes_low c w i' hi' h) i hi
  rw [eqMask64, mask8_bit (fun w => pack8 (eqLanes c w)) hf w0 w1 w2 w3 w4 w5 w6 w7 k j hk hj]
  generalize blockWord w0 w1 w2 w3 w4 w5 w6 w7 k = w
  have := pack8_spec (eqLanes c w) (fun i hi h => eqLanes_low c w i hi h) j hj
  simp only [laneFlag] at this
  rw [this]
  exact eqLanes_spec c w j hj

end VbmSimdProofs
