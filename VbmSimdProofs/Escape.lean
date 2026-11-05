import VbmSimd.Escape
import VbmSimdProofs.Bits
/-! # Proof: `escaped` and `escOut` compute the escape machine (clause `[VS-2]`)

The kernel is two additions; an addition is a carry chain, and a carry chain is a sequential machine in disguise. The proof is an induction over the bit index with an invariant `Inv` that
relates the carries of the two additions at bit `i` to the machine's state `escSpec b pb i` and to whether byte `i - 1` is a (counted) backslash. The step of the induction is a statement about eight
Booleans, discharged by `decide` (256 cases: `inv_step`). The bridge from `BitVec.carry` to the machine is `BitVec.getLsbD_add` and `BitVec.carry_succ`. Standard axioms only; no `bv_decide`.

The statement is restricted to bytes that are not backslashes on purpose: the kernel does not mark the escaped backslashes inside a run, and the one consumer (`quote and not escaped`) never asks about a
backslash (`quote_not_escaped_spec`). -/
namespace VbmSimdProofs
open VbmSimd

def evenM : BitVec 64 := 0x5555555555555555#64
def oddM : BitVec 64 := 0xAAAAAAAAAAAAAAAA#64
/-- the carried escape bit as a word (0 or 1). -/
def pv (pb : Bool) : BitVec 64 := if pb then 1#64 else 0#64

/-- the machine, on bit vectors (`escSpec`). -/
def escSpecB (B : BitVec 64) (pb : Bool) : Nat → Bool
  | 0 => pb
  | i + 1 => B.getLsbD i && !escSpecB B pb i

theorem escSpec_eq (b : UInt64) (pb : Bool) (i : Nat) : escSpec b pb i = escSpecB b.toBitVec pb i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [escSpec, escSpecB, bit, ih]

/-- the kernel on bit vectors: the escaped positions that are not backslashes. -/
def bsOf (B : BitVec 64) (pb : Bool) : BitVec 64 := B &&& ~~~(pv pb)
def startsOf (bs : BitVec 64) : BitVec 64 := bs &&& ~~~(bs <<< 1)
def escKernel (B : BitVec 64) (pb : Bool) : BitVec 64 :=
  let bs := bsOf B pb
  let st := startsOf bs
  let endsEv := (bs + (st &&& evenM)) &&& ~~~bs
  let endsOd := (bs + (st &&& oddM)) &&& ~~~bs
  (endsEv &&& oddM) ||| (endsOd &&& evenM) ||| pv pb
/-- the carry out of bit 63 of the odd-start addition. -/
def escOutK (B : BitVec 64) (pb : Bool) : Bool :=
  let bs := bsOf B pb
  decide ((bs + (startsOf bs &&& oddM)) < bs)

theorem even_bit (i : Nat) : evenM.getLsbD i = (decide (i < 64) && decide (i % 2 = 0)) := by
  by_cases h : i < 64
  · have : ∀ j : Fin 64, evenM.getLsbD j = decide (j.val % 2 = 0) := by decide
    simpa [h] using this ⟨i, h⟩
  · simp [h, BitVec.getLsbD_of_ge, show 64 ≤ i by omega]

theorem odd_bit (i : Nat) : oddM.getLsbD i = (decide (i < 64) && decide (i % 2 = 1)) := by
  by_cases h : i < 64
  · have : ∀ j : Fin 64, oddM.getLsbD j = decide (j.val % 2 = 1) := by decide
    simpa [h] using this ⟨i, h⟩
  · simp [h, BitVec.getLsbD_of_ge, show 64 ≤ i by omega]

theorem pv_bit (pb : Bool) (i : Nat) : (pv pb).getLsbD i = (pb && decide (i = 0)) := by
  cases pb
  · simp [pv]
  · by_cases h : i < 64
    · simp [pv, h]
    · simp [pv, BitVec.getLsbD_of_ge, show 64 ≤ i by omega, show i ≠ 0 by omega]

/-! The Bool-level step. State at position `i`: `a` = the byte before is a (counted) backslash; `cE`, `cO` = the carries into bit `i` of the two additions; `e` = the machine's value at `i`;
`odd` = `i` is odd; `z` = `i = 0`. -/
def Inv (a cE cO e odd z pb : Bool) : Bool :=
  (a || (!cE && !cO && (e == (z && pb)))) && (!a || ((cE ^^ cO) && (e == ((cE && odd) || (cO && !odd)))))

def stepA (B z pb : Bool) : Bool := B && !(pb && z)
def stepE (B a z pb cE : Bool) (odd : Bool) : Bool := Bool.atLeastTwo (stepA B z pb) ((stepA B z pb && !a) && !odd) cE
def stepO (B a z pb cO : Bool) (odd : Bool) : Bool := Bool.atLeastTwo (stepA B z pb) ((stepA B z pb && !a) && odd) cO

theorem inv_step : ∀ (B a cE cO e odd z pb : Bool), (z → !a) = true → Inv a cE cO e odd z pb = true →
    Inv (stepA B z pb) (stepE B a z pb cE odd) (stepO B a z pb cO odd) (B && !e) (!odd) false pb = true := by decide

/-! The bridge: the kernel's words satisfy `Inv` at every bit. -/
def aprev (A : BitVec 64) : Nat → Bool
  | 0 => false
  | i + 1 => A.getLsbD i

theorem bs_bit (B : BitVec 64) (pb : Bool) (i : Nat) (hi : i < 64) : (bsOf B pb).getLsbD i = stepA (B.getLsbD i) (decide (i = 0)) pb := by
  simp only [bsOf, stepA, BitVec.getLsbD_and, BitVec.getLsbD_not, pv_bit, hi, decide_true, Bool.true_and]

theorem st_bit (A : BitVec 64) (i : Nat) (hi : i < 64) : (startsOf A).getLsbD i = (A.getLsbD i && !aprev A i) := by
  cases i with
  | zero =>
    simp only [startsOf, aprev, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
    cases A.getLsbD 0 <;> rfl
  | succ j => simp only [startsOf, aprev, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, Nat.add_sub_cancel, show ¬ (j + 1 < 1) by omega, decide_false, Bool.not_false, Bool.and_true]

theorem inv_all (B : BitVec 64) (pb : Bool) : ∀ i, i ≤ 64 →
    Inv (aprev (bsOf B pb) i) (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& evenM) false) (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& oddM) false)
      (escSpecB B pb i) (decide (i % 2 = 1)) (decide (i = 0)) pb = true := by
  intro i
  induction i with
  | zero => intro _; simp [Inv, aprev, escSpecB, BitVec.carry_zero]
  | succ i ih =>
    intro hi
    have hi' : i < 64 := by omega
    have h := inv_step (B.getLsbD i) (aprev (bsOf B pb) i) (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& evenM) false)
      (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& oddM) false) (escSpecB B pb i) (decide (i % 2 = 1)) (decide (i = 0)) pb
      (by cases i <;> simp [aprev]) (ih (by omega))
    have e1 : (bsOf B pb).getLsbD i = stepA (B.getLsbD i) (decide (i = 0)) pb := bs_bit B pb i hi'
    have e2 : aprev (bsOf B pb) (i + 1) = stepA (B.getLsbD i) (decide (i = 0)) pb := by simp only [aprev, e1]
    have par : decide (i % 2 = 0) = !decide (i % 2 = 1) := by rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
    have par' : decide ((i + 1) % 2 = 1) = !decide (i % 2 = 1) := by rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h, Nat.add_mod]
    have e3 : BitVec.carry (i + 1) (bsOf B pb) (startsOf (bsOf B pb) &&& evenM) false = stepE (B.getLsbD i) (aprev (bsOf B pb) i) (decide (i = 0)) pb
        (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& evenM) false) (decide (i % 2 = 1)) := by
      rw [BitVec.carry_succ]
      simp only [stepE, BitVec.getLsbD_and, st_bit _ i hi', even_bit, hi', e1, decide_true, Bool.true_and, par]
    have e4 : BitVec.carry (i + 1) (bsOf B pb) (startsOf (bsOf B pb) &&& oddM) false = stepO (B.getLsbD i) (aprev (bsOf B pb) i) (decide (i = 0)) pb
        (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& oddM) false) (decide (i % 2 = 1)) := by
      rw [BitVec.carry_succ]
      simp only [stepO, BitVec.getLsbD_and, st_bit _ i hi', odd_bit, hi', e1, decide_true, Bool.true_and]
    rw [e2, e3, e4, par', show escSpecB B pb (i + 1) = (B.getLsbD i && !escSpecB B pb i) from rfl, show decide (i + 1 = 0) = false by simp]
    exact h

theorem final_step : ∀ (a cE cO e o z pb : Bool), (z → !a) = true → Inv a cE cO e o z pb = true → (((cE && o) || (cO && !o)) || (pb && z)) = e := by decide

/-- the kernel's escaped positions agree with the machine at every byte that is not a backslash. -/
theorem escKernel_spec (B : BitVec 64) (pb : Bool) (i : Nat) (hi : i < 64) (hB : B.getLsbD i = false) :
    (escKernel B pb).getLsbD i = escSpecB B pb i := by
  have inv := inv_all B pb i (by omega)
  have hA : (bsOf B pb).getLsbD i = false := by rw [bs_bit B pb i hi, hB]; simp [stepA]
  have hst : (startsOf (bsOf B pb)).getLsbD i = false := by rw [st_bit _ i hi, hA]; rfl
  have par : decide (i % 2 = 0) = !decide (i % 2 = 1) := by rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
  have sE := BitVec.getLsbD_add hi (bsOf B pb) (startsOf (bsOf B pb) &&& evenM)
  have sO := BitVec.getLsbD_add hi (bsOf B pb) (startsOf (bsOf B pb) &&& oddM)
  simp only [escKernel, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, sE, sO, hA, hst, even_bit, odd_bit, pv_bit, hi, decide_true, Bool.true_and, par,
    Bool.false_and, Bool.false_xor, Bool.not_false, Bool.and_true]
  exact final_step _ _ _ _ _ _ _ (by cases i <;> simp [aprev]) inv

theorem carry64 (x y : BitVec 64) : BitVec.carry 64 x y false = decide ((x + y) < x) := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.carry, BitVec.lt_def, BitVec.toNat_add]
  have : x.toNat % 2 ^ 64 = x.toNat := Nat.mod_eq_of_lt hx
  have : y.toNat % 2 ^ 64 = y.toNat := Nat.mod_eq_of_lt hy
  simp only [Bool.toNat_false, Nat.add_zero, *]
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat
  · have : (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat - 2 ^ 64 := by omega
    simp [h, this]; omega
  · have : (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat := Nat.mod_eq_of_lt (by omega)
    simp [h, this]

theorem out_step : ∀ (a cE cO e pb : Bool), Inv a cE cO e false false pb = true → cO = e := by decide

/-- the carry out of the block is the machine's state after byte 63. -/
theorem escOutK_spec (B : BitVec 64) (pb : Bool) : escOutK B pb = escSpecB B pb 64 := by
  have inv := inv_all B pb 64 (by omega)
  simp only [escOutK, ← carry64]
  exact out_step _ _ _ _ _ (by simpa using inv)

/-! ## The `UInt64` forms the library runs -/

theorem pv_carryWord (pb : Bool) : (carryWord pb).toBitVec = pv pb := by cases pb <;> rfl

theorem escaped_toBitVec (b prev : UInt64) (pb : Bool) (h : prev = carryWord pb) : (escaped b prev).toBitVec = escKernel b.toBitVec pb := by
  subst h
  simp [escaped, escKernel, bsOf, startsOf, evenBits, oddBits, evenM, oddM, pv_carryWord]

/-- `[VS-2]` at every byte of the block that is not a backslash, bit `i` of `escaped b prev` is the machine's value `escSpec b pb i`. -/
theorem escaped_spec (b : UInt64) (pb : Bool) (i : Nat) (hi : i < 64) (hb : bit b i = false) :
    bit (escaped b (carryWord pb)) i = escSpec b pb i := by
  rw [escSpec_eq]; simp only [bit] at hb ⊢
  rw [escaped_toBitVec b _ pb rfl]; exact escKernel_spec _ pb i hi hb

theorem bs_false (b : UInt64) : b &&& ~~~(carryWord false) = b := by
  apply UInt64.toBitVec_inj.mp
  simp [carryWord]

theorem bsOf_false (B : BitVec 64) : bsOf B false = B := by
  simp only [bsOf, pv, Bool.false_eq_true, ite_false, BitVec.not_zero, BitVec.and_allOnes]

/-- `[VS-2]` the carry out: `escOut b prev` is the machine's state after the last byte, as a word. -/
theorem escOut_spec (b : UInt64) (pb : Bool) : escOut b (carryWord pb) = carryWord (escSpec b pb 64) := by
  rw [escSpec_eq]
  have h := escOutK_spec b.toBitVec pb
  have key : escOut b (carryWord pb) = carryWord (escOutK b.toBitVec pb) := by
    cases pb
    · simp only [escOut, bs_false]
      simp only [escOutK, bsOf_false, startsOf, carryWord, oddBits, oddM, UInt64.lt_iff_toBitVec_lt,
        UInt64.toBitVec_and, UInt64.toBitVec_add, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_not]
      simp
    · simp [escOut, escOutK, bsOf, startsOf, oddBits, oddM, pv, carryWord, UInt64.lt_iff_toBitVec_lt, UInt64.toBitVec_and, UInt64.toBitVec_add, UInt64.toBitVec_shiftLeft]
  rw [key, h]

/-- `[VS-2]` the consumer of `escaped`: the quotes that are not escaped. For a quote mask `q` disjoint from the backslash mask `b`, bit `i` of `q &&& ~~~(escaped b prev)` is
"a quote at `i` and the machine says byte `i` is not escaped". -/
theorem quote_not_escaped_spec (q b : UInt64) (pb : Bool) (hqb : q &&& b = 0) (i : Nat) (hi : i < 64) :
    bit (q &&& ~~~(escaped b (carryWord pb))) i = (bit q i && !escSpec b pb i) := by
  rw [bit_and, bit_not _ _ hi]
  by_cases hq : bit q i = true
  · have hb : bit b i = false := by
      have h0 : bit (q &&& b) i = false := by rw [hqb]; simp [bit]
      rw [bit_and, hq] at h0; simpa using h0
    rw [escaped_spec b pb i hi hb]
  · simp [Bool.not_eq_true] at hq
    simp [hq]

end VbmSimdProofs
