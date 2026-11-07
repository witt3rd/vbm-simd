import VbmSimd.Append
/-! # Proof: `appendBytes` is the concatenation of the slice (`[VS-13]`)

The model is `ByteArray.copySlice` at the end of the destination: with the offset at `t.size` and the length bounded by what `a` has, nothing of `t` is overwritten and nothing is kept after the copy, so the result is
`t` followed by `a.extract i (i + n)` (an `extract` past the end of `a` is cut at its end, as the runtime cuts the copy). -/
namespace VbmSimdProofs
open VbmSimd

/-- `[VS-13]` `appendBytes t a i n` is `t ++ a.extract i (i + n)`. -/
theorem appendBytes_spec (t a : ByteArray) (i n : USize) : appendBytes t a i n = t ++ a.extract i.toNat (i.toNat + n.toNat) := by
  unfold appendBytes
  rw [ByteArray.copySlice_eq_append]
  have a1 : t.extract 0 t.size = t := ByteArray.extract_zero_size
  have a3 : t.extract (t.size + min n.toNat (a.data.size - i.toNat)) t.data.size = ByteArray.empty := by
    apply ByteArray.extract_eq_empty_iff.mpr; show min t.data.size t.size ≤ _; omega
  rw [a1, a3, ByteArray.append_empty]

end VbmSimdProofs
