import VbmSimd.Shims
/-! # `VbmSimd.Inset`: membership masks of 64 bytes (the AVX2 classifier)

`inset64 a i s` is the 64-bit mask whose bit `p` says that byte `i + p` of `a` is one of the (at most four) bytes of the set `s`: the first step of a structural scanner, which asks one such question per byte class
(quote, backslash, operators, white space) of every block of 64 bytes. The machine is `insetSpec` (`[VS-12]`), one bit per byte; the compiled code runs `vbm_simd_inset64` (`include/vbm_simd.h`, trust ledger T12), a
vector search whose Lean body is that machine (the model), tested against it (`tests/ShimTest.lean`). Where the CPU has no AVX2 (`hasAvx2 ()`, `VbmSimd.Find`) a consumer does not call it: it runs its own proved portable kernel. -/
namespace VbmSimd

/-- The mask of the first `n` bits whose predicate holds: bit `p` is `f p` for `p < n`, `0` from `n` on (`n ≤ 64`). -/
def maskFrom (f : Nat → Bool) : Nat → UInt64
  | 0 => 0
  | n + 1 => maskFrom f n ||| (if f n then (1 : UInt64) <<< n.toUInt64 else 0)

/-- `[VS-12]` the membership machine: bit `p` of the mask for the block at `i` is set iff byte `i + p` exists and is in the set `s`; bytes at or past the end give `0`. -/
def insetSpec (a : ByteArray) (i : Nat) (s : UInt32) : UInt64 := maskFrom (fun p => decide (i + p < a.size) && inSet s (byteAt0 a (i + p))) 64

/-- The membership masks of the 64 bytes at `i`, by AVX2 (model: `insetSpec`). Total: `i` at or past the end gives `0`. `a` is borrowed. -/
@[extern "vbm_simd_inset64"] def inset64 (a : @& ByteArray) (i : USize) (s : UInt32) : UInt64 := insetSpec a i.toNat s

end VbmSimd
