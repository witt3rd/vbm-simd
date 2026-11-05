import VbmSimd.Spec
/-! # `VbmSimd.PrefixXor`: the prefix xor of a 64-bit mask (the carry-less multiply by all ones, written portably)

Used to turn a mask of quote positions into the mask of positions inside a string: bit `i` of the result is the xor of bits `0 .. i` of the input.
Six shift-xor steps; on x86-64 with PCLMULQDQ it is one multiply, and a vector shim may use that, tested against this function (it is the model). Proved: `VbmSimdProofs.PrefixXor`. -/
namespace VbmSimd

/-- Bit `i` of the result is the xor of bits `0 .. i` of `x` (`prefixXor_spec`, clause `[VS-1]`). -/
@[inline] def prefixXor (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 1); let x := x ^^^ (x <<< 2); let x := x ^^^ (x <<< 4); let x := x ^^^ (x <<< 8); let x := x ^^^ (x <<< 16); x ^^^ (x <<< 32)

/-- The prefix xor with a carry in `c` (`0` or `1`: the state before bit 0): bit `i` is `c` xor the xor of bits `0 .. i`. Bit 63 of the result is the carry out
(`prefixXorC_carry`). `0 - c` is all ones when `c = 1`. -/
@[inline] def prefixXorC (x c : UInt64) : UInt64 := prefixXor x ^^^ (0 - c)

end VbmSimd
