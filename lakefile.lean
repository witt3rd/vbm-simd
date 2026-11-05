import Lake
open System Lake DSL

package «vbm-simd» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The library: the model of the vector operations and the kernels built from them. Imports `Init` only (checked by Tier 1): this is what a consumer
compiles to C, to WASM and into its own artifact, so nothing from `Std` or `Lean` may be in its closure. -/
@[default_target]
lean_lib VbmSimd where
  globs := #[.andSubmodules `VbmSimd]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `VbmSimd` may import it). -/
lean_lib VbmSimdProofs where
  globs := #[.andSubmodules `VbmSimdProofs]
