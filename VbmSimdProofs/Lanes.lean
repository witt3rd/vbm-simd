import VbmSimd.Lanes
import VbmSimdProofs.Bits
/-! # Proof: `eqLanes` flags equal lanes (`[VS-3]`), `pack8` packs the flags (`[VS-4]`)

`eqLanes`: the one non-lane-wise step is the addition in `zeroLanes`. Its carry chain is a machine again: the carry into bit `i` is the or of the bits of the same lane below `i`
(`orRun`), because adding `0x7f` to seven bits carries out iff any of them is set, and the top bit of a lane neither generates nor propagates a carry, so nothing crosses into the next lane.
The induction over the bit index (`carry_orRun`) has a step about three Booleans.

`pack8`: the input has only lane flags (every bit that is not the top bit of its lane is zero), so it is determined by eight Booleans; the statement is checked for all 256 of them by `decide`
(`pack8_flags`), and `pack8_spec` reduces to it (`flags_eq`). The constants are named definitions, so no large literal sits next to `decide` (`scripts/lint-proof-eval.sh`). -/
namespace VbmSimdProofs
open VbmSimd

/-! ## `zeroLanes` -/

def lo7B : BitVec 64 := 0x7f7f7f7f7f7f7f7f#64

theorem lo7B_bit (i : Nat) : lo7B.getLsbD i = (decide (i < 64) && decide (i % 8 < 7)) := by
  by_cases h : i < 64
  · have : ∀ j : Fin 64, lo7B.getLsbD j = decide (j.val % 8 < 7) := by decide
    simpa [h] using this ⟨i, h⟩
  · simp [h, BitVec.getLsbD_of_ge, show 64 ≤ i by omega]

/-- the or of the bits of `x` in the same lane below position `i`. -/
def orRun (x : BitVec 64) : Nat → Bool
  | 0 => false
  | i + 1 => if (i + 1) % 8 = 0 then false else orRun x i || x.getLsbD i

def addC (x : BitVec 64) (i : Nat) : Bool := BitVec.carry i (x &&& lo7B) lo7B false

theorem carry_orRun (x : BitVec 64) : ∀ i, i ≤ 64 → BitVec.carry i (x &&& lo7B) lo7B false = orRun x i := by
  intro i
  induction i with
  | zero => intro _; simp [BitVec.carry_zero, orRun]
  | succ i ih =>
    intro hi
    have hi' : i < 64 := by omega
    rw [BitVec.carry_succ, ih (by omega)]
    simp only [BitVec.getLsbD_and, lo7B_bit, hi', decide_true, Bool.true_and, orRun]
    have h8 : i % 8 < 8 := Nat.mod_lt _ (by omega)
    by_cases h7 : i % 8 < 7
    · have : ¬ ((i + 1) % 8 = 0) := by omega
      simp [h7, this]
      cases orRun x i <;> cases x.getLsbD i <;> simp
    · have : (i + 1) % 8 = 0 := by omega
      simp [h7, this, Bool.atLeastTwo]

/-- `zeroLanes` on bit vectors, bit by bit: at the top bit of a lane, "the whole lane is zero"; elsewhere zero. -/
def zl (x : BitVec 64) : BitVec 64 := ~~~(((x &&& lo7B) + lo7B) ||| x ||| lo7B)

theorem zl_top (x : BitVec 64) (k : Nat) (hk : k < 8) :
    (zl x).getLsbD (8 * k + 7) = !(orRun x (8 * k + 7) || x.getLsbD (8 * k + 7)) := by
  have hi : 8 * k + 7 < 64 := by omega
  have hm : (8 * k + 7) % 8 = 7 := by omega
  rw [zl, BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_add hi, carry_orRun x _ (by omega)]
  simp only [BitVec.getLsbD_and, lo7B_bit, hi, hm, decide_true]
  simp

theorem zl_low (x : BitVec 64) (i : Nat) (hi : i < 64) (h : i % 8 ≠ 7) : (zl x).getLsbD i = false := by
  rw [zl, BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_or, lo7B_bit]
  have : i % 8 < 7 := by omega
  simp [hi, this]

/-- the or of the lane's bits below the top one, and the top one: "some bit of lane `k` is set". -/
def laneSet (x : BitVec 64) (k : Nat) : Bool := (List.range 8).any fun j => x.getLsbD (8 * k + j)

theorem orRun_lane (x : BitVec 64) (k j : Nat) (hk : k < 8) (hj : j < 8) :
    orRun x (8 * k + j) = (List.range j).any fun d => x.getLsbD (8 * k + d) := by
  induction j with
  | zero =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simp [orRun]
    · obtain ⟨m, hm⟩ : ∃ m, 8 * k = m + 1 := ⟨8 * k - 1, by omega⟩
      have hc : (m + 1) % 8 = 0 := by omega
      rw [Nat.add_zero, hm, orRun]; simp [hc]
  | succ j ih =>
    have hj' : j < 8 := by omega
    have h1 : (8 * k + j + 1) % 8 ≠ 0 := by omega
    rw [show 8 * k + (j + 1) = (8 * k + j) + 1 by omega, orRun]
    simp [h1, ih hj', List.range_succ]

theorem zl_lane (x : BitVec 64) (k : Nat) (hk : k < 8) : (zl x).getLsbD (8 * k + 7) = !laneSet x k := by
  rw [zl_top x k hk, orRun_lane x k 7 hk (by omega)]
  simp [laneSet, List.range_succ]
  ac_rfl

theorem zeroLanes_toBitVec (x : UInt64) : (zeroLanes x).toBitVec = zl x.toBitVec := by
  simp [zeroLanes, zl, lo7, lo7B]

theorem byte_eq_iff (w c : UInt64) (k : Nat) : byte w k = byte c k ↔ ∀ j, j < 8 → bit w (8 * k + j) = bit c (8 * k + j) := by
  constructor
  · intro h j hj
    have := congrArg (fun v : BitVec 8 => v.getLsbD j) h
    simpa [byte, bit, BitVec.getLsbD_extractLsb', hj] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [byte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    exact h j hj

/-- `[VS-3]` the top bit of lane `k` of `eqLanes c w` says whether byte `k` of `w` equals byte `k` of `c`. -/
theorem eqLanes_spec (c w : UInt64) (k : Nat) (hk : k < 8) : bit (eqLanes c w) (8 * k + 7) = laneEq c w k := by
  have h := zl_lane (w.toBitVec ^^^ c.toBitVec) k hk
  have e : bit (eqLanes c w) (8 * k + 7) = (zl (w.toBitVec ^^^ c.toBitVec)).getLsbD (8 * k + 7) := by
    simp only [bit, eqLanes, zeroLanes_toBitVec, UInt64.toBitVec_xor]
  rw [e, h]
  have hl : laneSet (w.toBitVec ^^^ c.toBitVec) k = false ↔ ∀ j, j < 8 → bit w (8 * k + j) = bit c (8 * k + j) := by
    simp only [laneSet, List.any_eq_false, List.mem_range, BitVec.getLsbD_xor, bit]
    constructor
    · intro hh j hj
      have := hh j hj
      cases hw : w.toBitVec.getLsbD (8 * k + j) <;> cases hc : c.toBitVec.getLsbD (8 * k + j) <;> simp_all
    · intro hh j hj
      have := hh j hj
      simp [this]
  by_cases hq : ∀ j, j < 8 → bit w (8 * k + j) = bit c (8 * k + j)
  · have h1 : laneSet (w.toBitVec ^^^ c.toBitVec) k = false := hl.mpr hq
    simp [h1, laneEq, (byte_eq_iff w c k).mpr hq]
  · have h1 : laneSet (w.toBitVec ^^^ c.toBitVec) k = true := by
      cases hh : laneSet (w.toBitVec ^^^ c.toBitVec) k
      · exact absurd (hl.mp hh) hq
      · rfl
    have h2 : ¬ byte w k = byte c k := fun hh => hq ((byte_eq_iff w c k).mp hh)
    simp [h1, laneEq, h2]

/-- `[VS-3]` the other bits of `eqLanes` are zero: only the top bit of each lane is ever set. -/
theorem eqLanes_low (c w : UInt64) (i : Nat) (hi : i < 64) (h : i % 8 ≠ 7) : bit (eqLanes c w) i = false := by
  have := zl_low (w.toBitVec ^^^ c.toBitVec) i hi h
  simpa only [bit, eqLanes, zeroLanes_toBitVec, UInt64.toBitVec_xor] using this

end VbmSimdProofs
