import VbmSimd.Classify
import VbmSimdProofs.Inset
import VbmSimdProofs.Shims
/-! # Proof: the class masks are the byte-at-a-time machine, and where they are stored (`[VS-14]`)

`classSpec` is the machine (`maskFrom` of the per-byte predicate); what is proved here is what a consumer uses: bit `p` of each mask is "byte `i + p` exists and its class bits meet the mask byte", and the word `r` of the
result of `classify64` is the mask `r`, for an `out` with room for four words. -/
namespace VbmSimdProofs
open VbmSimd

/-- `[VS-14]` bit `p` of the class mask of the block at `i`: the byte exists and its class bits meet `m`. -/
theorem bit_classSpec (a : ByteArray) (i : Nat) (t : ByteArray) (m : UInt8) (p : Nat) (hp : p < 64) :
    bit (classSpec a i t m) p = (decide (i + p < a.size) && ((classByte t (byteAt0 a (i + p)) &&& m) != 0)) := by
  unfold classSpec
  rw [bit_maskFrom _ 64 (Nat.le_refl _) p]
  simp [hp]

theorem stFull_size (a : ByteArray) (k : Nat) (w : UInt64) : (stFull a k w).size = a.size := by
  unfold stFull
  split
  · exact st64Model_size a k w
  · rfl

theorem ld64Model_stFull_self (a : ByteArray) (k : Nat) (w : UInt64) (hk : 8 * k + 8 ≤ a.size) : ld64Model (stFull a k w) (8 * k) = w := by
  unfold stFull
  simp only [hk, ↓reduceIte]
  exact ld64Model_st64Model_self a k w hk

theorem ld64Model_stFull_other (a : ByteArray) (k : Nat) (w : UInt64) (j : Nat) (hjk : j ≠ k) : ld64Model (stFull a k w) (8 * j) = ld64Model a (8 * j) := by
  unfold stFull
  split
  · exact ld64Model_st64Model_other a k w j hjk
  · rfl

/-- `[VS-14]` the compiled `classify64` is the model. -/
theorem classify64_spec (a : ByteArray) (i : USize) (t : ByteArray) (ms : UInt32) (out : ByteArray) : classify64 a i t ms out = classifyModel a i.toNat t ms out := rfl

/-- `[VS-14]` the result has the size of `out`. -/
theorem classify64_size (a : ByteArray) (i : Nat) (t : ByteArray) (ms : UInt32) (out : ByteArray) : (classifyModel a i t ms out).size = out.size := by
  unfold classifyModel
  simp only [stFull_size]

/-- `[VS-14]` word 0 of the result is the class mask for the first byte of `ms`, word 1 for the second, word 2 for the third and word 3 for the fourth (`out` has room for four words). -/
theorem classify_word0 (a : ByteArray) (i : Nat) (t : ByteArray) (ms : UInt32) (out : ByteArray) (h : 32 ≤ out.size) :
    ld64Model (classifyModel a i t ms out) 0 = classSpec a i t ms.toUInt8 := by
  unfold classifyModel
  rw [show (0 : Nat) = 8 * 0 by rfl, ld64Model_stFull_other _ 3 _ 0 (by omega), ld64Model_stFull_other _ 2 _ 0 (by omega), ld64Model_stFull_other _ 1 _ 0 (by omega),
    ld64Model_stFull_self _ 0 _ (by first | omega | (simp only [stFull_size]; omega))]

theorem classify_word1 (a : ByteArray) (i : Nat) (t : ByteArray) (ms : UInt32) (out : ByteArray) (h : 32 ≤ out.size) :
    ld64Model (classifyModel a i t ms out) 8 = classSpec a i t (ms >>> 8).toUInt8 := by
  unfold classifyModel
  rw [show (8 : Nat) = 8 * 1 by rfl, ld64Model_stFull_other _ 3 _ 1 (by omega), ld64Model_stFull_other _ 2 _ 1 (by omega),
    ld64Model_stFull_self _ 1 _ (by first | omega | (simp only [stFull_size]; omega))]

theorem classify_word2 (a : ByteArray) (i : Nat) (t : ByteArray) (ms : UInt32) (out : ByteArray) (h : 32 ≤ out.size) :
    ld64Model (classifyModel a i t ms out) 16 = classSpec a i t (ms >>> 16).toUInt8 := by
  unfold classifyModel
  rw [show (16 : Nat) = 8 * 2 by rfl, ld64Model_stFull_other _ 3 _ 2 (by omega), ld64Model_stFull_self _ 2 _ (by first | omega | (simp only [stFull_size]; omega))]

theorem classify_word3 (a : ByteArray) (i : Nat) (t : ByteArray) (ms : UInt32) (out : ByteArray) (h : 32 ≤ out.size) :
    ld64Model (classifyModel a i t ms out) 24 = classSpec a i t (ms >>> 24).toUInt8 := by
  unfold classifyModel
  rw [show (24 : Nat) = 8 * 3 by rfl, ld64Model_stFull_self _ 3 _ (by first | omega | (simp only [stFull_size]; omega))]

end VbmSimdProofs
