import VbmSimd.Shims
/-! # `VbmSimd.Append`: append a short run of bytes (`[VS-13]`)

`appendBytes t a i n` is `ByteArray.copySlice` with the destination offset at the end of `t`: the bytes `a[i, i + n)` (as many as `a` has) appended to `t`. The Lean runtime does it by a call that checks the
array's exclusiveness and capacity, then calls `memcpy`; for a short run (a number's lexeme, a string without escapes) that call is most of the cost. The compiled code runs `vbm_simd_append`
(`include/vbm_simd.h`, trust ledger T13): for at most 16 bytes, an unshared `t` with room and a run inside `a`, two overlapping 8-byte (or 4-, 2-, 1-byte) moves and a size update; the runtime's own `copySlice` otherwise.
The Lean body is the model (`copySlice`: the result is the same value whichever way it is computed), and `appendBytes_spec` (`VbmSimdProofs/Append.lean`) says what that value is. -/
namespace VbmSimd

/-- `[VS-13]` the bytes `a[i, i + n)` appended to `t` (fewer when `a` has fewer): `ByteArray.copySlice` at the end of `t` (the model; the compiled code is `vbm_simd_append`, which is that call for a long run, a shared `t` or no room). `t` is consumed, `a` is borrowed. -/
@[extern "vbm_simd_append"] def appendBytes (t : ByteArray) (a : @& ByteArray) (i n : USize) : ByteArray := a.copySlice i.toNat t t.size n.toNat false

end VbmSimd
