# 0001. vbm-simd: what it is, and the choices that shape it

**Status:** accepted at the first landing. **Owner:** the repository owner.

## Context

The structural stage of a fast JSON parser (and of any text scanner) is a bit-parallel kernel: classify 64 bytes into masks, fix up neighbour-dependent bits with carry tricks. The first user, vbm-json, wants hardware speed and a proof. The kernels
are not JSON-specific, so they live in their own repository, depended on by vbm-json as a pinned Lake dependency, and reusable by other VBM libraries.

## Decisions

1. **The specification is a one-bit-at-a-time machine, the implementation is 64-bit word code in Lean, and the theorem relates them for every input** (`docs/method.md`). There is no per-intrinsic model: Lean's C emitter has no unboxed vector type, so a vector value cannot be a Lean value;
   whole-block kernels are specified as functions from bytes to masks instead.
2. **Portable first.** The verified path is `UInt64` arithmetic and runs on x86-64, aarch64 and wasm32 alike. Hardware vector kernels (AVX2, AVX-512, NEON, WebAssembly simd128) are optional accelerators for the same Lean specification, each its own trusted shim with its own trust-ledger entry and an exhaustive or random differential test against the portable path; they are selected at build time, with no runtime dispatch inside the verified core, and the portable path is always available.
3. **A tiny trusted C layer.** `ld64`, `st64`, `ctz` and `st32` as `static inline` functions with Lean models: without them Lean's emitted code reaches about 350 MB/s for the classifier, with them about 880 MB/s (measured on a prototype). Each shim moves or counts bits and decides nothing.
4. **Standard axioms only; no `bv_decide`** (`docs/findings/bv-decide.md`). The axiom gate is never relaxed.
5. **Direct landing, mechanical gates.** The repository lands changes with the vendored vbm-land lander and Tier 1 on the rebased combination; Tier 2 (leanchecker, nanoda) runs after the merge.
6. **Public from its first public commit.** No internal names, hosts or paths (`scripts/lint.sh`).
