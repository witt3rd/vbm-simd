import VbmSimd.Bytes
import VbmSimdProofs.Shims
/-! # Proof: `zeroBytes n` is `n` zero bytes (`[VS-9]`): its data is `Array.replicate n 0`. -/
namespace VbmSimdProofs
open VbmSimd

theorem zeroSmall_data : ∀ n, (zeroSmall n).data = Array.replicate n 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [zeroSmall, ByteArray.data_push, ih, Array.replicate_succ]

theorem zeroBytes_data : ∀ n, (zeroBytes n).data = Array.replicate n 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [zeroBytes]
    by_cases h : n < 8
    · simp only [h, ↓reduceDIte]; exact zeroSmall_data n
    · simp only [h, ↓reduceDIte]
      have hh := ih (n / 2) (by omega)
      by_cases hm : n % 2 = 1
      · have e' : (zeroBytes (n / 2) ++ zeroBytes (n / 2)).data = Array.replicate (n - 1) 0 := by
          rw [ByteArray.data_append, hh, Array.replicate_append_replicate]; congr 1; omega
        simp only [hm, ↓reduceIte, ByteArray.data_push, e']
        rw [← Array.replicate_succ]; congr 1; omega
      · have e' : (zeroBytes (n / 2) ++ zeroBytes (n / 2)).data = Array.replicate n 0 := by
          rw [ByteArray.data_append, hh, Array.replicate_append_replicate]; congr 1; omega
        simp only [hm, ↓reduceIte, e']

/-- `[VS-9]` `zeroBytes n` has size `n` and every byte is zero. -/
theorem zeroBytes_spec (n : Nat) : (zeroBytes n).size = n ∧ ∀ i, byteAt0 (zeroBytes n) i = 0 := by
  refine ⟨?_, fun i => ?_⟩
  · show (zeroBytes n).data.size = n
    rw [zeroBytes_data]; simp
  · unfold byteAt0
    rw [zeroBytes_data]
    rw [Array.getD_eq_getD_getElem?]
    by_cases h : i < n
    · simp [h]
    · rw [Array.getElem?_eq_none (by simpa using h)]; rfl

end VbmSimdProofs
