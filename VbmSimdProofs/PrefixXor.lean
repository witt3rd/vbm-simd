import VbmSimd.PrefixXor
/-! # Proof: `prefixXor` computes the prefix xor (clause `[VS-1]`)

Method: the six-step cascade doubles the width of a window each step. `xw x i w` is the xor of the `w` bits of `x` ending at bit `i` (clipped at bit 0); the one fact about windows that
is needed is that a window splits at any point (`xw_add`). Then step `k` turns "bit `i` holds the window of width `w`" into "... of width `2w`" (`step`), and after six steps the window
is 64 wide, which covers `0 .. i` for every `i < 64` (`xw_stable`, `xw_full`). Only the three standard axioms; no `bv_decide` (it adds one non-standard assumption per theorem, which a standard-axioms-only gate rejects). -/
namespace VbmSimdProofs
open VbmSimd

/-- xor of `x_(i-d)` for `d < w`, `d ≤ i`: the window of width `w` ending at bit `i`. -/
def xw (x : BitVec 64) (i : Nat) : Nat → Bool
  | 0 => false
  | w + 1 => xw x i w ^^ (decide (w ≤ i) && x.getLsbD (i - w))

theorem xw_add (x : BitVec 64) (i w v : Nat) : xw x i (w + v) = (xw x i w ^^ (decide (w ≤ i) && xw x (i - w) v)) := by
  induction v with
  | zero => simp [xw]
  | succ v ih =>
    rw [← Nat.add_assoc, xw, ih, xw]
    by_cases h1 : w ≤ i
    · by_cases h2 : v ≤ i - w
      · have h3 : w + v ≤ i := by omega
        have h4 : i - (w + v) = i - w - v := by omega
        simp [h1, h2, h3, h4]
      · have h3 : ¬ (w + v ≤ i) := by omega
        simp [h1, h2, h3]
    · have h2 : ¬ (w + v ≤ i) := by omega
      simp [h1, h2]

/-- the shift-xor cascade of the kernel, on bit vectors. -/
def px (x : BitVec 64) : BitVec 64 :=
  let x := x ^^^ (x <<< 1); let x := x ^^^ (x <<< 2); let x := x ^^^ (x <<< 4); let x := x ^^^ (x <<< 8); let x := x ^^^ (x <<< 16); x ^^^ (x <<< 32)

theorem step (x y : BitVec 64) (w : Nat) (h : ∀ i, i < 64 → y.getLsbD i = xw x i w) :
    ∀ i, i < 64 → (y ^^^ (y <<< w)).getLsbD i = xw x i (w + w) := by
  intro i hi
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, xw_add, h i hi]
  by_cases hw : w ≤ i
  · have : i - w < 64 := by omega
    simp [hi, hw, h _ this, show ¬ i < w by omega]
  · simp [hw, show i < w by omega]

/-- the machine `scanXor` on bit vectors. -/
def scanXorB (x : BitVec 64) : Nat → Bool
  | 0 => x.getLsbD 0
  | i + 1 => scanXorB x i ^^ x.getLsbD (i + 1)

theorem scanXor_eq (x : UInt64) (i : Nat) : scanXor x i = scanXorB x.toBitVec i := by
  induction i with
  | zero => simp [scanXor, scanXorB, bit]
  | succ i ih => simp [scanXor, scanXorB, bit, ih]

theorem xw_full (x : BitVec 64) (i : Nat) : xw x i (i + 1) = scanXorB x i := by
  induction i with
  | zero => simp [xw, scanXorB]
  | succ i ih =>
    have e1 : xw x (i + 1) 1 = x.getLsbD (i + 1) := by simp [xw]
    rw [show i + 1 + 1 = 1 + (i + 1) by omega, xw_add, e1, show i + 1 - 1 = i by omega, ih]
    simp [scanXorB, Bool.xor_comm]

theorem xw_stable (x : BitVec 64) (i w : Nat) (h : i < w) (v : Nat) : xw x i (w + v) = xw x i w := by
  rw [xw_add]; simp [show ¬ w ≤ i by omega]

/-- the cascade on bit vectors computes the prefix xor. -/
theorem px_spec (x : BitVec 64) (i : Nat) (hi : i < 64) : (px x).getLsbD i = scanXorB x i := by
  have h0 : ∀ i, i < 64 → x.getLsbD i = xw x i 1 := by intro i _; simp [xw]
  have h1 : ∀ i, i < 64 → (x ^^^ (x <<< 1)).getLsbD i = xw x i 2 := step x x 1 h0
  have h2 : ∀ i, i < 64 → ((x ^^^ (x <<< 1)) ^^^ ((x ^^^ (x <<< 1)) <<< 2)).getLsbD i = xw x i 4 := step x _ 2 h1
  have h3 := step x _ 4 h2
  have h4 := step x _ 8 h3
  have h5 := step x _ 16 h4
  have h6 := step x _ 32 h5
  have e : xw x i (32 + 32) = scanXorB x i := by
    rw [show 32 + 32 = (i + 1) + (63 - i) by omega, xw_stable x i (i + 1) (by omega), xw_full]
  rw [← e]; exact h6 i hi

theorem prefixXor_toBitVec (x : UInt64) : (prefixXor x).toBitVec = px x.toBitVec := by
  simp [prefixXor, px, UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft]

/-- `[VS-1]` bit `i` of `prefixXor x` is the xor of bits `0 .. i` of `x`, for every `i < 64`. -/
theorem prefixXor_spec (x : UInt64) (i : Nat) (hi : i < 64) : bit (prefixXor x) i = scanXor x i := by
  rw [scanXor_eq]; simp only [bit]; rw [prefixXor_toBitVec]; exact px_spec _ i hi

/-- `0 - 1` is all ones. -/
theorem zero_sub_one_bits (i : Nat) (hi : i < 64) : bit (0 - 1) i = true := by
  simp only [bit, UInt64.toBitVec_sub]
  have : (0 : UInt64).toBitVec - (1 : UInt64).toBitVec = BitVec.allOnes 64 := by
    have h0 : (0 : UInt64).toBitVec = 0#64 := rfl
    have h1 : (1 : UInt64).toBitVec = 1#64 := rfl
    rw [h0, h1, BitVec.zero_sub]; exact BitVec.neg_one_eq_allOnes
  rw [this]; simp only [BitVec.getLsbD_allOnes, hi, decide_true]

/-- `0 - c` is all ones for `c = 1` and zero for `c = 0`. -/
theorem zero_sub_carryWord (c : Bool) (i : Nat) (hi : i < 64) : bit (0 - carryWord c) i = c := by
  cases c
  · simp [carryWord, bit]
  · simpa [carryWord] using zero_sub_one_bits i hi

/-- `[VS-1]` with a carry in: bit `i` is `c` xor the xor of bits `0 .. i`. -/
theorem prefixXorC_spec (x : UInt64) (c : Bool) (i : Nat) (hi : i < 64) : bit (prefixXorC x (carryWord c)) i = (c ^^ scanXor x i) := by
  have h := prefixXor_spec x i hi
  have h2 := zero_sub_carryWord c i hi
  simp only [prefixXorC, bit, UInt64.toBitVec_xor, BitVec.getLsbD_xor] at h h2 ⊢
  rw [h, h2, Bool.xor_comm]

/-- `[VS-1]` the carry out is bit 63: the state after the block's last bit (the carry in to the next block). -/
theorem prefixXorC_carry (x : UInt64) (c : Bool) : bit (prefixXorC x (carryWord c)) 63 = (c ^^ scanXor x 63) := prefixXorC_spec x c 63 (by omega)

end VbmSimdProofs
