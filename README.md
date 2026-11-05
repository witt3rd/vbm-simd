# vbm-simd

Bit-parallel kernels for scanning text, **proved correct in Lean 4** against one-bit-at-a-time machines, and the very small amount of trusted C needed to run them at hardware speed.

> **Status: pre-release (early).** Six kernels are proved (prefix xor, escape carry, byte-lane compare, lane-flag packing, a 64-byte block mask, a cursor over the set bits of a mask array); four trusted C primitives are modelled and tested. Nothing is published to any package registry; build from source. The API will change.

## Why it exists

The fastest text scanners (simdjson, fast UTF-8 validators, CSV and HTTP splitters) all work the same way: classify 64 bytes at a time into bit masks, fix up the few bits that depend on their neighbours with
carry-propagating tricks (an addition whose carry chain finds escaped characters, a carry-less multiply that turns quote positions into "inside a string" positions), then work on the masks. They are fast and
they are subtle; a one-bit mistake in a carry trick is a parsing bug that no test finds, and they are written in C or intrinsics, without proof.

vbm-simd is the claim that the speed and the proof are one project. Each kernel is specified once as a tiny sequential machine that is obviously right, implemented as 64-bit word code in Lean (which compiles to
plain C, to WebAssembly and to the other Lean targets), and **proved equal to the machine for every input and every bit position**. What stays trusted is a handful of `static inline` C functions (a load, a store, a bit count) with
Lean models and differential tests, each with its own entry in a ledger. It is the shared core of [vbm-json](https://github.com/witt3rd/vbm-json)'s structural stage, and is meant for any library that scans bytes.

## What is proved today

| clause | the machine | the kernel | theorem |
|---|---|---|---|
| `VS-1` | the state after bit `i` is the xor of bits `0..i` | `prefixXor`, `prefixXorC` (six shift-xor steps, with a carry between blocks) | `prefixXor_spec`, `prefixXorC_spec` |
| `VS-2` | byte `i` is escaped iff the byte before it is a backslash that is not itself escaped | `escaped`, `escOut` (two additions; the carry out of the block) | `escaped_spec`, `escOut_spec`, `quote_not_escaped_spec` |
| `VS-3` | byte `k` of `w` equals byte `k` of `c` | `eqLanes` (SWAR compare of eight bytes at once) | `eqLanes_spec`, `eqLanes_low` |
| `VS-4` | the flag of lane `k` of a mask | `pack8` (eight lane flags to the low eight bits, one multiply) | `pack8_spec`, `pack8_high` |
| `VS-7` | the set positions of a mask array, in order | `cursorStart`, `cursorNext` (`ctz` and `x & (x - 1)`; no index array) | `cursorStart_spec`, `cursorNext_spec` |
| `VS-8` | bit `p` of a block mask comes from word `p / 8` | `mask8`, `eqMask64` (the mask of the bytes of a 64-byte block equal to a byte) | `mask8_bit`, `eqMask64_spec` |

**The trusted C** is one header, [`include/vbm_simd.h`](include/vbm_simd.h): `ld64`, `st64`, `st32`, `ctz`, each a few lines, each with a Lean model (`VbmSimd/Shims.lean`) that is its specification, tested against the model on boundary and random cases and against deliberate mutants of the header (`scripts/test-shims.sh`). They are total: no call touches memory outside its array.

The statements are about `UInt64` code, the code the Lean compiler turns into C, not about a model of it. Only the three standard axioms are used (checked by `scripts/AxiomGate.lean` on every run). [`docs/SPEC.md`](docs/SPEC.md) lists the clauses; [`docs/method.md`](docs/method.md) explains the proof pattern, which is the reusable part:
a carry chain is a sequential machine in disguise, so the proof is an induction over the bit index with an invariant relating the carry to the machine's state, whose step is a `decide` over a handful of Booleans.

`bv_decide`, the obvious tool for fixed-width circuits, is **not** used and cannot be: it adds one axiom per theorem, which the axiom gate rejects and the independent proof checkers can only take on trust ([`docs/findings/bv-decide.md`](docs/findings/bv-decide.md)).

## The ethos: verified bare metal (VBM)

VBM is a standard for libraries that are small, proved, and run on nothing; see [awesome-vbm](https://github.com/witt3rd/awesome-vbm). Here: the library imports only Lean's `Init`; nothing is allocated by the kernels; the proofs are about the code that runs; every hand-written line is in [`docs/trust-ledger.md`](docs/trust-ledger.md);
and coding agents wrote it under mechanical gates (forbidden constructs, the axiom gate, the spec-clause gate, the trust-ledger gate, each with a negative self-test showing it can fail) instead of line-by-line human review.

## Build and test

```sh
mise install                     # the pinned Lean release (mise.toml), no elan
mise exec -- lake build          # the library and the proofs, zero warnings
mise exec -- scripts/tier1.sh    # the whole gate: lints, build, axiom gate, spec clauses, trust ledger (about a minute)
mise exec -- scripts/tier2.sh    # the slow checks: leanchecker --fresh and the independent checker nanoda
```

## Contributing

The repository lands changes directly to `main` through a gate and does not take pull requests from outside; see [`AGENTS.md`](AGENTS.md) for the rules the agents work under. Issues are welcome.

## License

Apache-2.0. See [LICENSE](LICENSE).
