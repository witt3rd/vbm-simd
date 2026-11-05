import VbmSimd.Append
/-! # Proof: `appendBytes` is the append machine (`[VS-12]`) -/
namespace VbmSimdProofs
open VbmSimd

/-- `[VS-12]` the bytes of `appendBytes a b` are the bytes of `a` followed by the bytes of `b`. -/
theorem appendBytes_spec (a b : ByteArray) : (appendBytes a b).data.toList = appendSpec a b := by
  simp [appendBytes, appendSpec, ByteArray.data_append]

end VbmSimdProofs
