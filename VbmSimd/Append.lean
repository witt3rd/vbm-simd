import VbmSimd.Spec
/-! # `VbmSimd.Append`: appending a byte array to another, in place when it can be

Lean's `a ++ b` on byte arrays is the runtime function `lean_byte_array_copy_slice`: a call that decodes two boxed `Nat`s, clamps, tests exclusivity and capacity, and only then copies. A scanner that builds a
report out of many small appends (a few bytes each) spends more on that bookkeeping than on the copy. `appendBytes a b` is the same function with the common case inline: when `a` is unshared and has room for
`b` the bytes are copied behind it; otherwise the runtime's own append runs. Its Lean body `a ++ b` is its specification (the model; the proofs use it, the compiled code runs `vbm_simd_append` of
`include/vbm_simd.h`); `appendBytes_spec` says what it computes (`[VS-12]`). Trust ledger entry T12. -/
namespace VbmSimd

/-- `a` followed by the bytes of `b` (model: `a ++ b`); in place when `a` is unshared and has room. -/
@[extern "vbm_simd_append"] def appendBytes (a : ByteArray) (b : @& ByteArray) : ByteArray := a ++ b

end VbmSimd
