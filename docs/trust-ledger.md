# The trust ledger

One file listing **everything outside our direct control that vbm-simd executes or depends on**: code we did not prove, code we did not write, and facilities we assume. It exists because
*verified by construction* is the first priority of the project: the size of the unverified base, and the care taken at its boundary, is the most important measure. A boundary with no entry here
does not land (`scripts/trust-ledger-check.sh`, Tier 1).

**Snapshot at the first landing:** no C and no `@[extern]`: the library was Lean only, and the kernels are proved against the machines of `docs/SPEC.md`. The ledger covered what the *build* depends on.

**Snapshot at the shims (T10):** the portable shim header `include/vbm_simd.h` (four `static inline` functions, about 60 lines of C with comments) is the first and only trusted C. The vector-instruction shims (AVX2, AVX-512, NEON, WebAssembly simd128) arrive in their own landings, **one entry each**, each with its Lean model and a differential test against the portable path.

## How the gate keeps this file true

The set of things that must appear here is **derived from the tree, not from this file**: every `@[extern]` symbol under `VbmSimd/`, every header under `include/`, every `.github/workflows/` file, the build
pins (`lean-toolchain`, `mise.toml`, `lakefile.lean`), the vendored lander's pin (`scripts/land/PIN`), the Lean pin's compiler, runtime and bundled clang/ld.lld (the keys `lean-compiler`,
`lean-runtime`, `clang-lld`), and a watch-list of tools the scripts run. Each is a key (`file:`, `extern:`, `tool:`, plus the three Lean keys) that an entry must name on its **Covers** line.
- A new boundary (extern, header, workflow, tool) with no entry **fails**. A `Covers` key that names nothing real fails, and **removing any entry fails** (the gate does this to itself on every run, one entry at a time: an entry that covers nothing required is padding).
  Dangling file references fail. An entry needs all seven fields, a **Plan** from `verify | replace | sandbox | accept` (`accept` needs `because ...`), **Assumes** that links a written contract or says `no written contract`
  (counted as a gap), and **Test** that names a test that can fail or says `none` (counted as a gap).
- Not covered by the gate (said here rather than pretended): a tool called from a script that is not on the watch-list in `scripts/trust-ledger-check.sh`, and the *quality* of an entry's prose.

Entry format: **What** it is; **Enters** where it enters; **Assumes** what we assume of it (the contract); **Test** the test that can fail; **Owner**; **Plan**; **Covers** the derived keys.

## The Lean toolchain (pinned: one Lean release for the whole tree)

### T01. The Lean compiler: frontend, kernel, C emitter
- **What:** the `lean` release pinned in `lean-toolchain` and `mise.toml`: the elaborator, the kernel that checks every proof, and `EmitC`, which turns the library's definitions into the C a consumer links. A kernel soundness bug would void the proofs; an emitter bug would give the C different semantics from the Lean. Nothing proves the emitter preserves semantics.
- **Enters:** `lean-toolchain`, `mise.toml`; every `.lean` file.
- **Assumes:** the kernel is sound and `EmitC` is faithful: no written contract beyond Lean's own documentation. The differential tests of the shims and the consumers' vectors are the check on the emitted code; `leanchecker` and nanoda are the checks on the kernel (T02).
- **Test:** scripts/tier2.sh (leanchecker `--fresh`, nanoda); the emitter is checked only by the consumers' tests.
- **Owner:** upstream Lean (leanprover/lean4); the repository owner pins it (CODEOWNERS).
- **Plan:** accept, because there is no other mature route from Lean to C, WASM and the other targets and the kernel is small and independently re-checked; revisit when an extractor with a semantics-preservation proof exists.
- **Covers:** `lean-compiler` `file:lean-toolchain` `file:mise.toml`

### T02. The independent proof checkers: leanchecker, nanoda
- **What:** `leanchecker --fresh` replays every declaration in a fresh environment (guards a tampered or stale `.olean`); nanoda (`nanoda_bin`, shipped in the Lean release) re-checks the exported proofs with an independent kernel implementation.
- **Enters:** `scripts/tier2.sh` (run by CI on a schedule); they read the build products and the `leanexport` of both libraries.
- **Assumes:** that two independent checkers agreeing is evidence the kernel did not mis-accept; no written contract.
- **Test:** none that can fail on a bad proof here today: Tier 2 is the check; a deliberately false theorem in a scratch file is the planned negative test (a gap, counted).
- **Owner:** upstream Lean.
- **Plan:** verify. Add a negative self-test (a corrupted export must fail nanoda).
- **Covers:** `tool:leanchecker` `tool:nanoda`

### T03. The Lean runtime and its headers (lean.h, libleanrt)
- **What:** the C runtime every Lean-emitted C file links: reference counting, allocation, arrays and strings, big numbers. It is the lowest layer under the compiled kernels. This library's kernels are `UInt64` arithmetic (no allocation) so the part that runs is small; it is not checked by us.
- **Enters:** the Lean release pinned in `lean-toolchain`; the emitted C of `VbmSimd` includes `lean.h`.
- **Assumes:** the runtime implements Lean's object model correctly; no written contract.
- **Test:** none of ours: exercised through the consumers' tests.
- **Owner:** upstream Lean; the owner pins the version.
- **Plan:** accept, because the runtime is part of the one Lean release we pin and no verified replacement exists; the library imports `Init` only so the part that runs stays small.
- **Covers:** `lean-runtime`

### T04. clang and ld.lld (the compiler and linker the Lean release bundles)
- **What:** the C compiler and linker bundled in the Lean release, used by `lake`/`leanc` to compile Lean's emitted C. A miscompile changes the program the proofs were about.
- **Enters:** `lean-toolchain` (the bundle comes with the pin); `lakefile.lean` (every `lean_lib` build).
- **Assumes:** the compiler preserves C semantics for the emitted code; no written contract.
- **Test:** none of ours today; the check is the consumers' vectors run against the compiled artifact, and the differential tests the shims will carry.
- **Owner:** upstream LLVM via the Lean release; the owner pins it.
- **Plan:** sandbox. Check compiled artifacts against the Lean models with differential tests in CI, never trust the compile.
- **Covers:** `clang-lld`

## The build and process tools

### T05. Lake and the build file
- **What:** `lake` (shipped in the Lean release) reads `lakefile.lean` and builds both libraries; the file sets `warningAsError` and `autoImplicit false` and declares the two module roots (`VbmSimd`, `VbmSimdProofs`), the first Init-only.
- **Enters:** `lakefile.lean`; every `lake build` and `lake env lean --run` in `scripts/`.
- **Assumes:** the build builds the files that are in the tree and nothing else; the root split and the Init-only rule are enforced by Tier 1, not by Lake (scripts/tier1.sh: the import scan).
- **Test:** scripts/tier1.sh (zero-warning check with its negative case; the import scan with its negative cases).
- **Owner:** the repository owner (CODEOWNERS: `lakefile.lean`).
- **Plan:** accept, because Lake is the Lean toolchain's own build tool and a change to it is a toolchain change (T01).
- **Covers:** `file:lakefile.lean` `tool:lake`

### T06. mise: installs the pinned Lean release
- **What:** `mise` downloads and installs the Lean release tarball named in `mise.toml` from GitHub releases and puts it on `PATH` for `mise exec -- ...`.
- **Enters:** `mise.toml`; every script is run as `mise exec -- scripts/...`.
- **Assumes:** the tarball is the one released for that tag; no checksum is verified by us today (no written contract): a supply-chain gap.
- **Test:** none: nothing here can fail if the tarball were swapped (a gap, counted).
- **Owner:** the repository owner (`mise.toml`); mise is upstream.
- **Plan:** sandbox. Pin the release checksum in a lockfile once CI exists; until then the tarball's integrity is GitHub's.
- **Covers:** `tool:mise`

### T07. git, gh, python3: the process tooling
- **What:** `git` and `gh` (the rebase and push steps of the lander), `python3` (the trust-ledger and workflow checkers). They run on the developer's machine and in CI; none is part of any artifact.
- **Enters:** `scripts/land-direct` and the vendored `scripts/land/`, `scripts/trust_ledger.py`, the Tier 1 scripts.
- **Assumes:** they do what their manuals say; the self-tests of the scripts that use them are the check that our use is right; no written contract.
- **Test:** scripts/spec-check.sh; the lander's own suite lives in its source repository.
- **Owner:** upstream tools; the repository owner approves the scripts (CODEOWNERS).
- **Plan:** accept, because they touch the process and not the artifact: a compromised tool could land a bad change, which the gates and the owner's review are there to catch.
- **Covers:** `tool:git` `tool:gh` `tool:python3`

### T08. The CI runner and workflow actions (.github/workflows/ci.yml)
- **What:** `ci.yml` runs `scripts/tier1.sh` on every push to `main` and `scripts/tier2.sh` every six hours and on manual dispatch, on GitHub-hosted `ubuntu-latest` runners only (`scripts/lint-workflows.py` fails Tier 1 on a self-hosted label, on a `pull_request_target` trigger and on any secret other than the default token). No pull-request trigger, so a fork's code never runs with the repository's token. Three third-party actions, pinned by commit sha: `actions/checkout` v4, `actions/cache` v4, `jdx/mise-action` v2. Token: the default `GITHUB_TOKEN`, `contents: read`; no secrets.
- **Enters:** `.github/workflows/ci.yml`; every CI run. It runs only on GitHub: it cannot be run locally.
- **Assumes:** the runner image, the pinned action commits and the cache behave as documented; a poisoned cache or a compromised upstream action could change what is checked. There is no written contract beyond GitHub's documentation.
- **Test:** none that can fail inside this repository (the workflow cannot run locally); none.
- **Owner:** the repository owner (CODEOWNERS); the actions are upstream.
- **Plan:** sandbox. Keep the permissions read-only and secret-free; the actions are pinned to commit shas; the cache never replaces the gates.
- **Covers:** `file:.github/workflows/ci.yml`

### T09. The vendored lander (scripts/land/, a pinned copy of vbm-land)
- **What:** `scripts/land/` and the stub `scripts/land-direct` are a pinned, vendored copy of vbm-land (a language-neutral direct-landing tool): the lock, the red check, the rebase, Tier 1 on the exact combination, the fast-forward push. `scripts/land/bin/land-check` (run in Tier 1) fails when any file differs from the manifest named by `scripts/land/PIN`. A bug in it could land a change that skipped a gate; it never touches the artifact.
- **Enters:** `scripts/land/`, `scripts/land-direct`, `scripts/land.conf`; every landing.
- **Assumes:** the lander does what its source repository's README documents; the drift check keeps the copy equal to the pinned release; no written contract here.
- **Test:** `scripts/land/MANIFEST.sha256`, checked against every vendored file by `scripts/land/bin/land-check` in Tier 1 (a drifted copy fails; the lander's own tests are in its source repository).
- **Owner:** the vbm-land repository (same owner); the pin is changed only by `scripts/land/bin/land-update`.
- **Plan:** accept, because the tool is what the owner's other repositories use and its failure modes are mechanical refusals; the independent push CI re-runs Tier 1 on what it landed.
- **Covers:** `file:scripts/land/PIN`

## The trusted C

### T10. The portable shim header: include/vbm_simd.h (`ld64`, `st64`, `st32`, `ctz`)
- **What:** the first 60 lines of `include/vbm_simd.h` (the byte search below is T11): four `static inline` functions, each the body of an `@[extern]` function of `VbmSimd/Shims.lean` whose Lean body is its specification (the model): `vbm_simd_ld64` (an 8-byte little-endian load from a Lean `ByteArray`, zero past the end), `vbm_simd_st64` and `vbm_simd_st32` (8- and 4-byte little-endian stores, in place when the array is unshared, copied first when shared, nothing written past the end), `vbm_simd_ctz` (count of trailing zero bits, 64 for zero; `__builtin_ctzll`). They exist because Lean's emitted C for byte-at-a-time assembly is 2.4 times slower than one load or store. Each is total (no out-of-range access, no precondition), moves or counts bits and decides nothing. A wrong load, a store through a shared array, or a miscount would be a bug no Lean proof sees: they are the unverified base of every kernel built on them.
- **Enters:** `include/vbm_simd.h`; every consumer compiles its generated C with `-include include/vbm_simd.h` (the repository's own `shim-test` and the `lean_lib` do, `lakefile.lean`); the four `@[extern]` symbols `vbm_simd_ld64`, `vbm_simd_st64`, `vbm_simd_st32`, `vbm_simd_ctz`.
- **Assumes:** the Lean models of `VbmSimd/Shims.lean` (the specification, in `docs/SPEC.md` clauses VS-5 and VS-6); a little-endian host with GCC or clang builtins (the header refuses others at compile time); the Lean runtime's `lean_sarray_*` functions behave as `lean.h` documents (T03); a Lean `ByteArray` is a scalar array of bytes.
- **Test:** `scripts/test-shims.sh` runs `tests/ShimTest.lean` (about 32000 comparisons of each C function against its model: every array size 0 to 41 with every index through, at and past the end including the largest `USize`; every single-bit and bit-pair word for `ctz`, 20000 random; a shared array must be copied) and then builds six deliberate mutants of the header (a wrong offset, a skipped copy-on-share, a wrong zero case, two skipped partial stores) in scratch copies, each of which the same test must catch (T11 and T12 add their own mutants to the same list).
- **Owner:** the repository owner (CODEOWNERS: `include/`).
- **Plan:** verify, in part: exhaustive testing is impossible for 64-bit inputs, so the argument is the boundary and random cases plus mutants; a formal model of the C (a verified C compiler's semantics) would replace the argument and is out of scope. The header stays small on purpose.
- **Covers:** `file:include/vbm_simd.h` `extern:vbm_simd_ld64` `extern:vbm_simd_st64` `extern:vbm_simd_st32` `extern:vbm_simd_ctz`

### T11. The AVX2 byte search and the CPU test: include/vbm_simd.h (`vbm_simd_find_avx2`, `vbm_simd_has_avx2`)
- **What:** about 55 more lines of the same header: `vbm_simd_find_avx2`, the C body of `findAvx2` (`VbmSimd/Find.lean`), the first index at or after `i` of a byte in a set of at most four bytes, `n` (the size) when there is none or `i >= n`; 32 bytes per step with one 256-bit compare per member (clang vector extensions and `__builtin_ia32_pmovmskb256`: the Lean toolchain ships no intrinsics header), the last partial step done by one load of the last 32 bytes of the array with the bits of the bytes before `i` shifted out, arrays under 32 bytes by the scalar loop `vbm_simd_find_scalar` (which is also the whole function on a CPU or compiler without the AVX2 body). `vbm_simd_has_avx2` (CPUID leaf 7 AVX2 bit, leaf 1 OSXSAVE and AVX bits, XCR0 bits 1 and 2) is the C body of `hasAvx2`; `findFirstOf` takes the shim only when it says yes and otherwise runs `findSwar`, which is Lean, proved, and not trusted. The shim decides nothing the model does not: its Lean body is `findSpec` (`[VS-11]`), and `findFirstOf_spec` is proved for either answer of the CPU test. A wrong index, a read past the end (a fault, or a silent wrong answer from bytes that are not the array's), a dropped member or a wrong CPU answer (AVX2 instructions on a CPU without them: SIGILL) would be bugs no Lean proof sees.
- **Enters:** `include/vbm_simd.h`; the two `@[extern]` symbols `vbm_simd_find_avx2` and `vbm_simd_has_avx2` (`VbmSimd/Find.lean`); every consumer that calls `findFirstOf`, compiled with `-include include/vbm_simd.h` as for T10.
- **Assumes:** the model `findSpec` (`docs/SPEC.md` clause VS-11); an x86-64 CPU's `cpuid` and `xgetbv` report truthfully, and an AVX2 CPU with the OS saving the vector state runs the instructions the compiler emits for `target("avx2")`; clang's vector extensions compile `==`, `|` on 32-byte vectors to compare and or (the compiler is T04); `lean_sarray_cptr` and `lean_sarray_size` describe the array (T03). The non-x86 or non-clang build (the scalar loop, `has_avx2` 0) is not exercised by Tier 1, which runs on x86-64 with clang; its scalar loop is the one the tests do exercise.
- **Test:** `scripts/test-shims.sh` runs `tests/ShimTest.lean` (about 17 million comparisons: the AVX2 shim, the proved portable search and the dispatch against `findSpec` for four sets, every size 0 to 70 and the boundaries 95 to 97, 127 to 129, 255 to 257 and 1000, a member planted at every position or none, every byte a member, random dense arrays, every start through past the end and the largest `USize`; `hasAvx2` against the `avx2` flag of `/proc/cpuinfo`) and `tests/find_guard.c` (about 11 million cases of the C functions against a naive loop on buffers flush against an unmapped page at the end and at the start, so any read outside the buffer is a SIGSEGV), then ten deliberate mutants of the header (an over-read, bits kept from before the start, a shift off by one, a dropped member, no bounds guard, a wrong tail load, a wrong index, a dropped scalar member, a scalar loop that restarts, a wrong CPUID bit), each of which one of the two must catch.
- **Owner:** the repository owner (CODEOWNERS: `include/`).
- **Plan:** verify, in part: the test is the boundary, planted and random cases plus guard pages and mutants, not a proof of the C; the portable path is proved in Lean, so a doubt about the shim is settled by taking it out (the dispatch falls back to `findSwar`). The other vector sets (AVX-512, NEON, simd128) each get their own entry.
- **Covers:** `extern:vbm_simd_find_avx2` `extern:vbm_simd_has_avx2`

### T12. The AVX2 membership masks: include/vbm_simd.h (`vbm_simd_inset64`)
- **What:** about 45 more lines of the same header: `vbm_simd_inset64`, the C body of `inset64` (`VbmSimd/Inset.lean`), the 64-bit mask of the block of 64 bytes at `i` whose bit `p` says that byte `i + p` is a member of a set of at most four bytes (as in T11), 0 for a byte at or past the end and for an `i` at or past the end. It is the classifier of a structural scanner (quote, backslash, operator, white space masks of every block): two 256-bit loads, one compare per member (clang vector extensions and `__builtin_ia32_pmovmskb256`), one movemask each; a block that crosses the end is the last 64 bytes of the array (all inside it) with the bits of the bytes before `i` shifted out, an array under 64 bytes the scalar loop `vbm_simd_inset64_scalar` (which is also the whole function on a CPU or compiler without the AVX2 body). It uses T11's CPU test: a consumer calls it only where `hasAvx2 ()` is true and runs its own proved portable kernel otherwise, so the shim decides nothing the model does not: its Lean body is `insetSpec` (`[VS-12]`). A wrong mask bit, a read past the end or a dropped member would be bugs no Lean proof sees (a consumer's proof takes the model for the C).
- **Enters:** `include/vbm_simd.h`; the `@[extern]` symbol `vbm_simd_inset64` (`VbmSimd/Inset.lean`); every consumer that calls `inset64`, compiled with `-include include/vbm_simd.h` as for T10.
- **Assumes:** the model `insetSpec` (`docs/SPEC.md` clause VS-12); the CPU-test assumptions of T11 (the AVX2 instructions run where `hasAvx2 ()` says so); clang's vector extensions compile `==` and `|` on 32-byte vectors to compare and or (T04); `lean_sarray_cptr` and `lean_sarray_size` describe the array (T03). The non-x86 or non-clang build is the scalar loop, not exercised by Tier 1 apart from the guard test, which runs the scalar loop on every size.
- **Test:** `scripts/test-shims.sh` runs `tests/ShimTest.lean` (the AVX2 masks against `insetSpec` for nine sets, among them the set that contains the byte 0 and the JSON classes, every size 0 to 140 and the boundaries 191 to 193, 255 to 257 and 1000, a member planted at every position or at the lane and block boundaries, every byte a member, all zero, random dense arrays, every start through past the end and the largest `USize`; every byte value at the lane boundaries 0, 1, 15, 16, 17, 31, 32, 33, 62 to 65 for every set) and `tests/find_guard.c` (the C functions against a naive loop on buffers flush against an unmapped page at the end and at the start, so any read outside the buffer is a SIGSEGV), then seven deliberate mutants of the header (an over-read, bits kept from before the start, a dropped member, no bounds guard, a wrong tail load, a wrong short-array case, a scalar loop that ignores the start), each of which one of the two must catch.
- **Owner:** the repository owner (CODEOWNERS: `include/`).
- **Plan:** verify, in part, as T11: the test is the boundary, planted, per-byte and random cases plus guard pages and mutants, not a proof of the C; the consumer's portable path is proved in Lean, so a doubt about the shim is settled by taking it out (the dispatch falls back to the portable kernel).
- **Covers:** `extern:vbm_simd_inset64`
