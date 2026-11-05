import VbmSimd.Shims
/-! # `VbmSimd.Bytes`: a zero-filled byte array of a given size

The mask array a scanner fills (`st64`) must already have its size: `ByteArray.empty` has none, and `Array.replicate n 0` converted to a `ByteArray` allocates and copies `n` boxed elements.
`zeroBytes n` doubles: `log n` appends of an array to itself (each one `memcpy`), `2n` bytes copied in all. Proved: `VbmSimdProofs.Bytes` (`[VS-9]`). -/
namespace VbmSimd

/-- `n` zero bytes, one `push` each (for `n` below the doubling threshold). -/
def zeroSmall : Nat → ByteArray
  | 0 => ByteArray.empty
  | n + 1 => (zeroSmall n).push 0

/-- `[VS-9]` A byte array of `n` zero bytes, built by doubling (`zeroBytes_spec`). -/
def zeroBytes (n : Nat) : ByteArray :=
  if _h : n < 8 then zeroSmall n
  else
    let half := zeroBytes (n / 2)
    let r := half ++ half
    if n % 2 = 1 then r.push 0 else r
termination_by n
decreasing_by omega

end VbmSimd
