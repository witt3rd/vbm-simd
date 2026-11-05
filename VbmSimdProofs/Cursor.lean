import VbmSimd.Cursor
import VbmSimdProofs.Shims
import VbmSimdProofs.Mask
/-! # Proof: the bit cursor walks the set bits in order (`[VS-7]`)

Three layers. (1) `clearLowest x` is `x` without its lowest set bit: `~~~(x - 1) = -x`, and the library knows the bits of `-x` (`BitVec.getLsbD_neg`: bit `i` of `-x` is `x_i` xor "some lower bit is set"), so bit `i` of
`x &&& (x - 1)` is `x_i` and "some lower bit is set". (2) With `ctz` (`[VS-6]`) that gives `bitsOf x = ctz x :: bitsOf (clearLowest x)`, by three small facts about `posFrom` (skipping a zero prefix, agreeing
masks, a hit). (3) `seek` (move to the next non-empty word) does not change the stream and leaves the cursor normal (`m ≠ 0` or no later word); so `cursorStart` stands for all the set bits, and
`cursorNext` for the rest after the one at `curPos`. -/
namespace VbmSimdProofs
open VbmSimd

/-! ## (1) clearing the lowest bit -/

theorem sub_one_eq_not_neg (x : BitVec 64) : x - 1#64 = ~~~(-x) := by
  have h : ~~~(x - 1#64) = -x := by rw [BitVec.not_sub_one_eq_not_add_one, BitVec.neg_eq_not_add]
  rw [← h, BitVec.not_not]

/-- bit `i` of `x &&& (x - 1)`: `x_i` and some lower bit is set. -/
theorem clearLowest_bit (x : UInt64) (i : Nat) (hi : i < 64) :
    bit (clearLowest x) i = true ↔ bit x i = true ∧ ∃ j, j < i ∧ bit x j = true := by
  have h1 : (x - 1).toBitVec = ~~~(-x.toBitVec) := by
    rw [UInt64.toBitVec_sub]; exact sub_one_eq_not_neg x.toBitVec
  have h2 : bit (clearLowest x) i = (x.toBitVec.getLsbD i && !((-x.toBitVec).getLsbD i)) := by
    simp only [clearLowest, bit, UInt64.toBitVec_and, BitVec.getLsbD_and, h1, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  rw [h2, BitVec.getLsbD_neg]
  simp only [bit]
  by_cases hx : x.toBitVec.getLsbD i = true
  · have hx' : x.toBitVec[i] = true := by rw [← BitVec.getLsbD_eq_getElem hi]; exact hx
    simp [hx', hi]
  · have hx' : ¬ x.toBitVec[i] = true := by rw [← BitVec.getLsbD_eq_getElem hi]; exact hx
    simp
    intro hh; exact absurd hh hx

/-! ## (2) the positions of the set bits -/

theorem posFrom_zero_prefix (m : UInt64) (i : Nat) : ∀ k f, (∀ j, i ≤ j → j < i + k → bit m j = false) → posFrom m (k + f) i = posFrom m f (i + k) := by
  intro k
  induction k generalizing i with
  | zero => intro f _; simp
  | succ k ih =>
    intro f h
    have h0 : bit m i = false := h i (Nat.le_refl _) (by omega)
    rw [show k + 1 + f = (k + f) + 1 by omega, posFrom, h0]
    simp only [Bool.false_eq_true, ite_false]
    rw [ih (i + 1) f (fun j h1 h2 => h j (by omega) (by omega)), show i + 1 + k = i + (k + 1) by omega]

theorem posFrom_congr (m m' : UInt64) : ∀ f i, (∀ j, i ≤ j → j < i + f → bit m j = bit m' j) → posFrom m f i = posFrom m' f i := by
  intro f
  induction f with
  | zero => intro i _; rfl
  | succ f ih =>
    intro i h
    have h0 := h i (Nat.le_refl _) (by omega)
    rw [posFrom, posFrom, h0, ih (i + 1) (fun j h1 h2 => h j (by omega) (by omega))]

theorem posFrom_hit (m : UInt64) (f i : Nat) (h : bit m i = true) : posFrom m (f + 1) i = i :: posFrom m f (i + 1) := by
  simp [posFrom, h]

theorem posFrom_zero (f i : Nat) : posFrom 0 f i = [] := by
  induction f generalizing i with
  | zero => rfl
  | succ f ih => simp [posFrom, bit, ih]

/-- the set positions of `x ≠ 0`: the position of the lowest set bit, then those of `x` without it. -/
theorem bitsOf_cons (x : UInt64) (hx : x ≠ 0) : bitsOf x = (ctzModel x).toNat :: bitsOf (clearLowest x) := by
  obtain ⟨hlt, hset, hlow⟩ := ctzModel_spec x hx
  generalize hc : (ctzModel x).toNat = c at hlt hset hlow ⊢
  have hbit : ∀ j, bit (clearLowest x) j = true ↔ bit x j = true ∧ j ≠ c := by
    intro j
    by_cases hj : j < 64
    · rw [clearLowest_bit x j hj]
      constructor
      · rintro ⟨hxj, k, hk, hkx⟩
        refine ⟨hxj, fun hjc => ?_⟩
        subst hjc
        rw [hlow k hk] at hkx; exact absurd hkx (by simp)
      · rintro ⟨hxj, hjc⟩
        have hcj : c < j := by
          refine Nat.lt_of_le_of_ne ?_ (Ne.symm hjc)
          exact Nat.le_of_not_lt fun hjlt => by rw [hlow j hjlt] at hxj; exact absurd hxj (by simp)
        exact ⟨hxj, c, hcj, hset⟩
    · have h1 := bit_ge (clearLowest x) j (by omega)
      have h2 := bit_ge x j (by omega)
      simp [h1, h2]
  have hc0 : ∀ j, j < c → bit (clearLowest x) j = false := by
    intro j hj
    have := hlow j hj
    cases h : bit (clearLowest x) j
    · rfl
    · have := (hbit j).mp h; rw [hlow j hj] at this; exact absurd this.1 (by simp)
  have hcc : bit (clearLowest x) c = false := by
    cases h : bit (clearLowest x) c
    · rfl
    · exact absurd rfl ((hbit c).mp h).2
  unfold bitsOf
  have e1 : posFrom x 64 0 = posFrom x (c + (64 - c)) 0 := by congr 1; omega
  rw [e1, posFrom_zero_prefix x 0 c (64 - c) (fun j _ hj => by simpa using hlow j (by omega)), Nat.zero_add,
    show 64 - c = (63 - c) + 1 by omega, posFrom_hit x _ c hset]
  have e2 : posFrom (clearLowest x) 64 0 = posFrom (clearLowest x) ((c + 1) + (63 - c)) 0 := by congr 1; omega
  rw [e2, posFrom_zero_prefix (clearLowest x) 0 (c + 1) (63 - c) (fun j _ hj => by
        by_cases hjc : j < c
        · exact hc0 j hjc
        · have : j = c := by omega
          subst this; exact hcc), Nat.zero_add]
  congr 1
  apply posFrom_congr
  intro j h1 h2
  cases hx' : bit x j <;> cases hc' : bit (clearLowest x) j <;> try rfl
  · have := (hbit j).mp hc'; rw [hx'] at this; exact absurd this.1 (by simp)
  · have : bit x j = true ∧ j ≠ c := ⟨hx', by omega⟩
    rw [← hbit j] at this; rw [hc'] at this; exact absurd this (by simp)

/-! ## (3) the cursor -/

theorem bitsOf_zero : bitsOf 0 = [] := posFrom_zero 64 0

theorem streamFrom_lt (ws : Nat → UInt64) (n w : Nat) (h : w < n) : streamFrom ws n w = (bitsOf (ws w)).map (64 * w + ·) ++ streamFrom ws n (w + 1) := by
  rw [streamFrom]; simp only [h, ↓reduceIte]

theorem streamFrom_ge (ws : Nat → UInt64) (n w : Nat) (h : n ≤ w) : streamFrom ws n w = [] := by
  rw [streamFrom]; simp only [show ¬ w < n by omega, ↓reduceIte]

/-- a cursor at the end stands for nothing. -/
theorem curStream_end (ws : Nat → UInt64) (n w : Nat) (hn : n ≤ w + 1) : curStream ws n w 0 = [] := by
  simp [curStream, bitsOf_zero, streamFrom_ge ws n (w + 1) hn]

theorem seek_succ_pos (masks : ByteArray) (n f w : Nat) (m : UInt64) (h : (m == 0 && decide (w + 1 < n)) = true) :
    seek masks n (f + 1) w m = seek masks n f (w + 1) (wordAt masks (w + 1)) := by
  simp only [seek, h, ↓reduceIte]

theorem seek_succ_neg (masks : ByteArray) (n f w : Nat) (m : UInt64) (h : ¬ (m == 0 && decide (w + 1 < n)) = true) :
    seek masks n (f + 1) w m = (w, m) := by
  simp [seek, h]

/-- `seek` does not change what the cursor stands for. -/
theorem seek_stream (masks : ByteArray) (n : Nat) : ∀ f w m, curStream (wordAt masks) n (seek masks n f w m).1 (seek masks n f w m).2 = curStream (wordAt masks) n w m := by
  intro f
  induction f with
  | zero => intro w m; rfl
  | succ f ih =>
    intro w m
    by_cases hc : (m == 0 && decide (w + 1 < n)) = true
    · have hc' := hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
      obtain ⟨hm, hw⟩ := hc'
      rw [seek_succ_pos _ _ _ _ _ hc, ih]
      subst hm
      simp [curStream, bitsOf_zero, streamFrom_lt (wordAt masks) n (w + 1) hw]
    · rw [seek_succ_neg _ _ _ _ _ hc]

/-- `seek` leaves the cursor normal: a non-empty word, or no later word, once the fuel covers the words. -/
theorem seek_norm (masks : ByteArray) (n : Nat) : ∀ f w m, n ≤ f + (w + 1) → (seek masks n f w m).2 ≠ 0 ∨ n ≤ (seek masks n f w m).1 + 1 := by
  intro f
  induction f with
  | zero => intro w m h; right; simp [seek]; omega
  | succ f ih =>
    intro w m h
    by_cases hc : (m == 0 && decide (w + 1 < n)) = true
    · rw [seek_succ_pos _ _ _ _ _ hc]; exact ih (w + 1) _ (by omega)
    · rw [seek_succ_neg _ _ _ _ _ hc]
      by_cases hm : m = 0
      · right
        have : ¬ (w + 1 < n) := by intro hw; exact hc (by simp [hm, hw])
        omega
      · left; exact hm

/-- `[VS-7]` the cursor at the start stands for every set bit of the words, and is normal. -/
theorem cursorStart_spec (masks : ByteArray) :
    curStream (wordAt masks) (wordCount masks) (cursorStart masks).1 (cursorStart masks).2 = streamFrom (wordAt masks) (wordCount masks) 0 ∧
    ((cursorStart masks).2 ≠ 0 ∨ wordCount masks ≤ (cursorStart masks).1 + 1) := by
  refine ⟨?_, seek_norm masks _ _ _ _ (by omega)⟩
  unfold cursorStart
  rw [seek_stream]
  by_cases h : 0 < wordCount masks
  · rw [streamFrom_lt _ _ 0 h]; rfl
  · have hsz : masks.size = 0 := by unfold wordCount at h; omega
    have h0 : wordAt masks 0 = 0 := by
      have : masks.data.size = 0 := hsz
      simp [wordAt, ld64, ld64Model, byteAt0, this]
    rw [streamFrom_ge _ _ 0 (by omega), h0]
    simp [curStream, bitsOf_zero, streamFrom_ge (wordAt masks) (wordCount masks) 1 (by omega)]

/-- `[VS-7]` a normal cursor with `m ≠ 0` yields `curPos w m`, and the cursor after it stands for the rest; that cursor is normal. -/
theorem cursorNext_spec (masks : ByteArray) (w : Nat) (m : UInt64) (hm : m ≠ 0) :
    curStream (wordAt masks) (wordCount masks) w m = curPos w m :: curStream (wordAt masks) (wordCount masks) (cursorNext masks w m).1 (cursorNext masks w m).2 ∧
    ((cursorNext masks w m).2 ≠ 0 ∨ wordCount masks ≤ (cursorNext masks w m).1 + 1) := by
  refine ⟨?_, seek_norm masks _ _ _ _ (by omega)⟩
  unfold cursorNext
  rw [seek_stream]
  simp only [curStream, curPos, bitsOf_cons m hm, List.map_cons, List.cons_append]
  rfl

/-! ## The stream is the filter of the positions -/

theorem posFrom_eq_filter (m : UInt64) : ∀ f i, posFrom m f i = (List.range' i f).filter (fun k => bit m k) := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ f ih =>
    intro i
    rw [List.range'_succ, List.filter_cons, posFrom, ih (i + 1)]

theorem posFrom_map (m : UInt64) (c : Nat) : ∀ f i, (posFrom m f i).map (c + ·) = (List.range' (c + i) f).filter (fun k => bit m (k - c)) := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ f ih =>
    intro i
    rw [List.range'_succ, List.filter_cons, posFrom]
    have e : c + i + 1 = c + (i + 1) := by omega
    rw [e]
    cases h : bit m i
    · simpa [ih (i + 1)] using h
    · simp [ih (i + 1), h]

/-- The set positions of the words `w .. n - 1`, as a filter of the bit positions `64 w .. 64 n - 1`. -/
theorem streamFrom_eq (ws : Nat → UInt64) (n : Nat) : ∀ d w, n - w = d →
    streamFrom ws n w = (List.range' (64 * w) (64 * d)).filter (fun k => bit (ws (k / 64)) (k % 64)) := by
  intro d
  induction d with
  | zero => intro w h; rw [streamFrom_ge ws n w (by omega)]; rfl
  | succ d ih =>
    intro w h
    rw [streamFrom_lt ws n w (by omega), ih (w + 1) (by omega)]
    have e : List.range' (64 * w) (64 * (d + 1)) = List.range' (64 * w) 64 ++ List.range' (64 * (w + 1)) (64 * d) := by
      have h1 := @List.range'_append (64 * w) 64 (64 * d) 1
      rw [show 64 * (d + 1) = 64 + 64 * d by omega, ← h1, show 64 * w + 1 * 64 = 64 * (w + 1) by omega]
    rw [e, List.filter_append]
    congr 1
    rw [bitsOf, posFrom_map, Nat.add_zero]
    apply List.filter_congr
    intro k hk
    have hk' := List.mem_range'_1.mp hk
    rw [show k - 64 * w = k % 64 by omega, show k / 64 = w by omega]

/-- `[VS-7]` the cursor at the start stands for exactly the set bits of the mask words, as a filter of the bit positions. -/
theorem cursorStart_filter (masks : ByteArray) :
    curStream (wordAt masks) (wordCount masks) (cursorStart masks).1 (cursorStart masks).2 =
      (List.range (64 * wordCount masks)).filter (fun k => bit (wordAt masks (k / 64)) (k % 64)) := by
  rw [(cursorStart_spec masks).1, streamFrom_eq (wordAt masks) (wordCount masks) (wordCount masks - 0) 0 rfl, List.range_eq_range']
  simp

/-! ## The next set bit at or after a position -/

/-- Bit `k` (counted over the whole mask array) of the words `ws`. -/
def bitPos (ws : Nat → UInt64) (k : Nat) : Bool := bit (ws (k / 64)) (k % 64)

theorem nextSetGo_spec (masks : ByteArray) (n L : Nat) : ∀ f w m,
    (∀ i, i < 64 → bit m i = (bitPos (wordAt masks) (64 * w + i) && decide (L ≤ 64 * w + i))) →
    (∀ k, L ≤ k → k < 64 * w → bitPos (wordAt masks) k = false) → L < 64 * (w + 1) → w < n → n ≤ w + f →
    L ≤ nextSetGo masks n f w m ∧ nextSetGo masks n f w m ≤ 64 * n ∧ (∀ k, L ≤ k → k < nextSetGo masks n f w m → bitPos (wordAt masks) k = false) ∧
      (nextSetGo masks n f w m = 64 * n ∨ bitPos (wordAt masks) (nextSetGo masks n f w m) = true) := by
  intro f
  induction f with
  | zero => intro w m _ _ _ hw hf; omega
  | succ f ih =>
    intro w m hm hb hc hw hf
    by_cases hz : m = 0
    · have hall : ∀ i, i < 64 → L ≤ 64 * w + i → bitPos (wordAt masks) (64 * w + i) = false := by
        intro i hi hLi
        have := hm i hi
        rw [hz] at this
        have h0 : bit (0 : UInt64) i = false := by simp [bit]
        rw [h0] at this
        have hLi' : decide (L ≤ 64 * w + i) = true := by simpa using hLi
        rw [hLi'] at this
        simpa using this.symm
      have hb' : ∀ k, L ≤ k → k < 64 * (w + 1) → bitPos (wordAt masks) k = false := by
        intro k hLk hk
        by_cases hk' : k < 64 * w
        · exact hb k hLk hk'
        · have := hall (k - 64 * w) (by omega) (by omega)
          rwa [show 64 * w + (k - 64 * w) = k by omega] at this
      rw [nextSetGo]
      simp only [hz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hn : w + 1 < n
      · simp only [hn, ↓reduceIte]
        apply ih (w + 1) _ _ hb' (by omega) hn (by omega)
        intro i hi
        have h : decide (L ≤ 64 * (w + 1) + i) = true := by simp; omega
        rw [h]
        simp only [bitPos, Bool.and_true]
        rw [show (64 * (w + 1) + i) / 64 = w + 1 by omega, show (64 * (w + 1) + i) % 64 = i by omega]
      · simp only [hn, ↓reduceIte]
        refine ⟨by omega, Nat.le_refl _, fun k hLk hk => hb' k hLk (by omega), Or.inl trivial⟩
    · obtain ⟨hlt, hset, hlow⟩ := ctzModel_spec m hz
      generalize hc' : (ctzModel m).toNat = c at hlt hset hlow
      have hr : nextSetGo masks n (f + 1) w m = 64 * w + c := by
        rw [nextSetGo]
        have : (m != 0) = true := by simpa using hz
        simp only [this, ↓reduceIte]
        show 64 * w + (ctzModel m).toNat = _
        rw [hc']
      rw [hr]
      have hbc := hm c hlt
      rw [hset] at hbc
      have hbc' : bitPos (wordAt masks) (64 * w + c) = true ∧ L ≤ 64 * w + c := by simpa using hbc.symm
      refine ⟨hbc'.2, by omega, fun k hLk hk => ?_, Or.inr hbc'.1⟩
      by_cases hk' : k < 64 * w
      · exact hb k hLk hk'
      · have h1 := hm (k - 64 * w) (by omega)
        rw [hlow (k - 64 * w) (by omega), show 64 * w + (k - 64 * w) = k by omega] at h1
        have hLk' : decide (L ≤ k) = true := by simpa using hLk
        rw [hLk'] at h1
        simpa using h1.symm

/-- `[VS-10]` `nextSet masks j` is the first set bit at or after `j` (or the end, `64 * wordCount masks`, when there is none). -/
theorem nextSet_spec (masks : ByteArray) (j : Nat) (hj : j ≤ 64 * wordCount masks) :
    j ≤ nextSet masks j ∧ nextSet masks j ≤ 64 * wordCount masks ∧ (∀ k, j ≤ k → k < nextSet masks j → bitPos (wordAt masks) k = false) ∧
      (nextSet masks j = 64 * wordCount masks ∨ bitPos (wordAt masks) (nextSet masks j) = true) := by
  unfold nextSet
  simp only []
  by_cases hw : j / 64 < wordCount masks
  · simp only [hw, ↓reduceIte]
    apply nextSetGo_spec masks (wordCount masks) j (wordCount masks - j / 64) (j / 64) _ _ _ (by omega) hw (by omega)
    · intro i hi
      have h0 : bit (~~~(0 : UInt64)) (i - j % 64) = true := by rw [bit_not _ _ (by omega)]; simp [bit]
      have e1 : (64 * (j / 64) + i) / 64 = j / 64 := by omega
      have e2 : (64 * (j / 64) + i) % 64 = i := by omega
      rw [bit_and, bit_shl _ _ (by omega) _ hi, h0]
      simp only [Bool.and_true, bitPos]
      by_cases h : j % 64 ≤ i
      · have h1 : decide (j % 64 ≤ i) = true := by simpa using h
        have h2 : decide (j ≤ 64 * (j / 64) + i) = true := by simp; omega
        rw [h1, h2, e1, e2]
      · have h1 : decide (j % 64 ≤ i) = false := by simpa using h
        have h2 : decide (j ≤ 64 * (j / 64) + i) = false := by simp; omega
        rw [h1, h2, e1, e2]
    · intro k hk hk'; omega
  · simp only [hw, ↓reduceIte]
    refine ⟨by omega, Nat.le_refl _, fun k hk hk' => by omega, Or.inl trivial⟩

end VbmSimdProofs
