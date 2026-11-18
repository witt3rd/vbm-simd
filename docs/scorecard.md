# Scorecard

Status: draft by a worker, 2026-11-18; goals and targets are the owner's to set.

This is vbm-simd's own scorecard: how well the repository is doing against the goals it states for itself. Every goal below cites where the repository says it; every metric is an integer, with its unit in its name. Values were measured on 2026-11-18 on an x86-64 Linux box with AVX2 (4 cores, the machine was loaded by other jobs), from the repository root, with the pinned Lean 4.35.0 already on `PATH` (the jail had no network, so `mise exec --` could not install; with a network, prefix each `lake`/`scripts/` command with `mise exec --`). The floor starts equal to `now`: it may only move toward better.

## Goals as the repository states them

1. **Proved, not tested: every kernel is proved equal to a one-bit-at-a-time machine for every input and bit position.** `README.md:3`, `README.md:13`; `AGENTS.md:17-18`; `docs/decisions/0001-vbm-simd.md:12`.
2. **No kernel without its clause, machine and theorem; no unproved claim called verified.** `AGENTS.md:31`; `CONTRIBUTING.md:20`; `docs/SPEC.md:3-5`.
3. **The unverified base is as small and as well guarded as possible: "the size of the unverified base, and the care taken at its boundary, is the most important measure".** Every trusted thing has exactly one ledger entry, a Lean model and a test that can fail. `docs/trust-ledger.md:3-5`; `AGENTS.md:32`; `CONTRIBUTING.md:22`; `docs/decisions/0001-vbm-simd.md:15`.
4. **Standard axioms only; no `sorry`/`admit`/`axiom`/`unsafe`/`implemented_by`/`csimp`, no `bv_decide`, `native_decide` or `decide +kernel`.** `AGENTS.md:29-30`; `README.md:32-35`; `docs/decisions/0001-vbm-simd.md:16`.
5. **The library imports `Init` only (and its own modules), so it compiles to C, WASM and other Lean targets.** `AGENTS.md:33`; `README.md:13`, `README.md:39`; `lakefile.lean:7-8`.
6. **Hardware speed: the portable path is always available, vector shims (AVX2, NEON; later AVX-512, simd128) are optional accelerators, each tested against its model.** `README.md:3`, `README.md:13-15`; `docs/decisions/0001-vbm-simd.md:14-15`; `AGENTS.md:32`.
7. **A zero-warning build, and a gate in which a check that never ran cannot pass.** `README.md:46`; `lakefile.lean:5`; `docs/decisions/0002-ran-evidence.md:1-3`.
8. **Everything runs before the push, once; nothing after; main stays green.** `AGENTS.md:5`, `AGENTS.md:10`; `CONTRIBUTING.md:13-14`.
9. **Cover the planned kernels: the UTF-8 validation automaton and the chunking theorem.** `docs/SPEC.md:24`; `AGENTS.md:24-25`.
10. **Reusable by other VBM libraries; pre-release, not yet in the VBM registry, nothing published to a package registry.** `README.md:5`, `README.md:15`; `AGENTS.md:19`.
11. **Public hygiene: no secrets, internal names or local paths.** `AGENTS.md:34`; `CONTRIBUTING.md:24`; `docs/decisions/0001-vbm-simd.md:18`.
12. **The public documents tell the truth about the tree** (the README is "the public face"; the ledger and SPEC are gate-checked). `AGENTS.md:21`; `README.md:5`.

## Metrics

| metric | direction | goal it serves | how to measure (from the repository root) | now (value, date) | floor (= now) | target |
|---|---|---|---|---|---|---|
| spec-clauses-count | higher | 1, 2, 9 | `grep -c '^\| VS-' docs/SPEC.md` | 14 (2026-11-18) | 14 | |
| planned-clauses-remaining-count | lower | 9 | `sed -n '24,25p' docs/SPEC.md \| grep -o -e 'UTF-8 validation automaton' -e 'chunking theorem' \| wc -l` | 2 (2026-11-18) | 2 | |
| proof-ledger-gaps-count (clauses with no machine tag or no tagged theorem, or tags that are not clauses) | lower | 1, 2 | `scripts/spec-check.sh 2>&1 \| grep -c -e 'not defined' -e 'not discharged' -e 'not a clause' -e 'no clause'` (prints 0 and exits 1 when clean; the script itself prints `ok (14 clauses ...)`) | 0 (2026-11-18) | 0 | |
| theorems-count (in `VbmSimdProofs/`) | higher | 1 | `grep -rhe '^theorem ' -e '^lemma ' -e '^private theorem ' -e '^private lemma ' -e '^protected theorem ' -e '^protected lemma ' VbmSimdProofs \| wc -l` | 129 (2026-11-18) | 129 | |
| proof-lines-per-library-line-permille (lines of `VbmSimdProofs*` per 1000 lines of `VbmSimd*`) | higher | 1 | `awk -v p=$(cat VbmSimdProofs.lean VbmSimdProofs/*.lean \| wc -l) -v l=$(cat VbmSimd.lean VbmSimd/*.lean \| wc -l) 'BEGIN{print int(p*1000/l)}'` | 3486 (2026-11-18; 1447 / 415 lines) | 3486 | |
| axiom-offending-constants-count | lower | 4 | `.land/tool/bin/land-lean axiom \| grep -o '[0-9]* offending'` | 0 (2026-11-18; 668 constants checked) | 0 | |
| forbidden-constructs-count (outside lines marked `tier1-allow`) | lower | 4 | `grep -rnw -e sorry -e admit -e axiom -e unsafe -e implemented_by -e csimp VbmSimd VbmSimdProofs VbmSimd.lean VbmSimdProofs.lean \| grep -vc tier1-allow` | 0 (2026-11-18) | 0 | |
| recheck-failures-count (every proof replayed by Lean's own checker in a fresh process; exit code) | lower | 1, 4 | `.land/tool/bin/land-lean recheck >/dev/null 2>&1; echo $?` | 0 (2026-11-18) | 0 | |
| build-warnings-count (build sets `warningAsError`, so a warning fails the build; a cached build prints none either way) | lower | 7 | `lake build VbmSimd VbmSimdProofs 2>&1 \| grep -ci warning` | 0 (2026-11-18) | 0 | |
| build-seconds (cold build of both libraries) | lower | 7 | `rm -rf .lake/build && ( time lake build VbmSimd VbmSimdProofs ) 2>&1 \| grep real` (the first build in a clean tree was timed) | 40 (2026-11-18) | 40 | |
| trusted-c-share-hundredths-of-percent (lines of `include/vbm_simd.h` over those plus the lines of `VbmSimd*`; the header's comments count) | lower | 3 | `awk -v c=$(wc -l < include/vbm_simd.h) -v l=$(cat VbmSimd.lean VbmSimd/*.lean \| wc -l) 'BEGIN{print int(c*10000/(c+l))}'` | 4546 (2026-11-18; 346 / 761 lines) | 4546 | |
| trusted-c-lines-count | lower | 3 | `wc -l < include/vbm_simd.h` | 346 (2026-11-18) | 346 | |
| trust-ledger-entries-count (one per trusted boundary; fewer boundaries is better, each must stay covered) | lower | 3 | `.land/tool/bin/land-lean trust --count` | 12 (2026-11-18) | 12 | |
| trust-ledger-gaps-count (entries with "no written contract" or a test of `none`) | lower | 3 | `.land/tool/bin/land-lean trust \| grep -o '[0-9]* with no written'` | 5 (2026-11-18) | 5 | |
| shim-comparisons-count (C shims against their Lean models, per run, this x86-64 AVX2 host) | higher | 3, 6 | `lake build shim-test && SHIM_TEST_NO_BENCH=1 .lake/build/bin/shim-test` (first number in the `ok` line) | 22817843 (2026-11-18) | 22817843 | |
| shim-test-seconds (the comparisons, no mutants, no bench) | lower | 8 | `lake build shim-test && ( time SHIM_TEST_NO_BENCH=1 .lake/build/bin/shim-test ) 2>&1 \| grep real` | 48 (2026-11-18) | 48 | |
| shim-mutants-defined-count (hand-made mutants of the header, all architectures) | higher | 3 | `awk '/^mutants=\(/{f=1;next} /^\)/{f=0} f && /^  "/' scripts/test-shims.sh \| wc -l` | 69 (2026-11-18; 43 are run on x86-64, the 26 `neon-` ones only on aarch64) | 69 | |
| shim-mutants-uncaught-count | lower | 3 | `scripts/test-shims.sh` (exits non-zero and names the mutant when one is not caught) | unmeasured: it builds 43 mutant copies of the tree in parallel (many minutes, heavy on the 31 GB shared by every lane); needs a box of its own, and an aarch64 box for the 26 NEON mutants | | |
| neon-comparisons-count | higher | 3, 6 | `SHIM_TEST_NO_BENCH=1 .lake/build/bin/shim-test` on aarch64 (the `NEON ...` counts in the `ok` line) | unmeasured: needs an aarch64 machine (0 on this x86-64 host, where the NEON bodies are not compiled) | | |
| tier1-seconds (the whole gate) | lower | 8 | `( time mise exec -- scripts/tier1.sh ) 2>&1 \| grep real` | unmeasured: runs the mutants (see above); a clean-container run of an earlier tree took 41 s (`docs/flip-record.md:29`), not comparable | | |
| bench-classify64-avx2-megabytes-per-second (informational; noisy, the host was loaded) | higher | 6 | `.lake/build/bin/shim-test \| grep 'bench classify64'` (the AVX2 figure) | 6272 (2026-11-18; the per-byte Lean loop 46) | 6272 | |
| bench-find-avx2-1024-megabytes-per-second (a member every 1024 bytes; informational, noisy) | higher | 6 | `.lake/build/bin/shim-test \| grep 'every 1024'` (the AVX2 figure) | 32600 (2026-11-18; portable `findSwar` 5122) | 32600 | |
| local-path-hits-count (tracked files that name a home, users or mount path) | lower | 11 | `git grep -n -e '/ho[m]e/' -e '/User[s]/' -e '/mn[t]/' \| wc -l` | 0 (2026-11-18) | 0 | |
| public-lint-violations-count (`scripts/lint.sh`, the lint named in `docs/decisions/0001-vbm-simd.md:18`) | lower | 11 | `scripts/lint.sh` | unmeasured: the script does not exist in this tree | | |
| readme-clauses-missing-count (clauses of `docs/SPEC.md` that the README's "What is proved today" table does not name) | lower | 12 | `for v in $(grep -o '^\| VS-[0-9]*' docs/SPEC.md \| grep -o 'VS-[0-9]*'); do grep -q "\`$v\`" README.md \|\| echo $v; done \| wc -l` | 6 (2026-11-18: VS-5, 6, 11, 12, 13, 14; the README also says "Thirteen clauses", the SPEC has 14) | 6 | |
| dangling-script-references-count (scripts named in the docs, the scripts or the tests that are not in `scripts/`) | lower | 12 | `for f in $(grep -ohE 'scripts/[A-Za-z0-9_.-]+[.](sh\|py\|txt)' README.md AGENTS.md CONTRIBUTING.md SECURITY.md docs/*.md docs/decisions/*.md docs/findings/*.md scripts/*.sh tests/* \| sort -u); do [ -e $f ] \|\| echo $f; done \| wc -l` | 8 (2026-11-18: `lib-ran.sh`, `lint-proof-eval.sh`, `lint-workflows.py`, `lint.sh`, `long-runners.txt`, `ran-evidence.sh`, `run-scoped.sh`, `test_ran_evidence.sh`) | 8 | |
| signed-release-tags-count (the VERSION file says 0.1.1) | higher | 10 | `git tag \| wc -l` | 0 (2026-11-18) | 0 | |

## Health today

- **Clean and at the floor:** the proofs and the proof gates (no clause without a theorem, 0 offending axioms, 0 forbidden constructs, every proof re-checked by Lean's own checker, 0 build warnings, no local paths). These are the project's strength; nothing has regressed, and there is no earlier value to regress from (this is the first reading).
- **Far from where the goals point:** the unverified base. Goal 3 calls it the most important measure, yet `trusted-c-share-hundredths-of-percent` is 4546 (the trusted header is nearly half of the lines that run) and `trust-ledger-gaps-count` is 5 (entries that say "no written contract" or a test of `none`). The gaps sit in the Lean toolchain, runtime, clang and mise entries (T01, T03, T04, T06) and python3 (T07); none can be closed by a proof here, only by accepting them or by a check (for T06, a pinned checksum).
- **Unmeasured:** `shim-mutants-uncaught-count`, `tier1-seconds` and `neon-comparisons-count` (the mutant run is too heavy for a shared box; NEON needs aarch64). The NEON bodies, a third of the mutants (26 of 69), have therefore never been seen run by this scorecard.
- **Documents out of step with the tree:** the README names 8 of 14 clauses and says thirteen; 8 scripts named in the docs and scripts are not in `scripts/` (among them `scripts/lint.sh`, which `docs/decisions/0001-vbm-simd.md:18` says enforces the no-private-names rule, so `public-lint-violations-count` cannot be measured). Whether the scripts were never vendored or were removed is not stated.
- **Release:** no tag, not in the VBM registry (`README.md:5`), two planned kernels not started (`planned-clauses-remaining-count` 2).

## What a steward would do first

1. Find out whether `scripts/lint.sh` and the other 7 scripts the docs name (`ran-evidence.sh`, `lib-ran.sh`, `test_ran_evidence.sh`, `run-scoped.sh`, ...) were lost or never landed, then restore them or correct the docs: this moves `dangling-script-references-count` (8 to 0) and makes `public-lint-violations-count` measurable.
2. Run the whole gate once on a box that can carry it (an x86-64 and an aarch64 one), to record `shim-mutants-uncaught-count`, `tier1-seconds` and `neon-comparisons-count`, so the three unmeasured rows get a value and a floor.
3. Bring the README table and its "Thirteen clauses" in line with `docs/SPEC.md` (VS-5, 6, 11, 12, 13, 14 missing), which moves `readme-clauses-missing-count` (6 to 0); then take the next kernel from `docs/SPEC.md:24` (the UTF-8 validation automaton), which moves `planned-clauses-remaining-count`, and for each trust-ledger gap decide to accept or close it, which moves `trust-ledger-gaps-count`.

## Questions for the owner

- Targets: none is stated in the repository, so the target column is empty. In particular, what share of trusted C is acceptable (`trusted-c-share-hundredths-of-percent`), and should `trust-ledger-gaps-count` reach 0 or are the five toolchain entries accepted for good?
- Is the trusted-C measure better taken in lines of the header, in lines excluding comments, or by the number of `@[extern]` symbols? (The header is mostly commented prose; the share here counts every line.)
- Are the speed figures a goal or only a note? The repository says "hardware speed" and gives an old figure (about 880 MB/s on a prototype, `docs/decisions/0001-vbm-simd.md:15`) but sets no threshold and no benchmark gate; the two bench rows are informational and noisy.
- Does a release (a signed tag, entry in the VBM registry, a first consumer pin by vbm-json) belong in the goals? `README.md:5` says pre-release and "unscored", with no condition for leaving that state.
- Are `scripts/lint.sh` and the ran-evidence scripts (`docs/decisions/0002-ran-evidence.md`) meant to exist in this repository? If not, decision 0002 and the README's mention of them should be revised.
- Is `trust-ledger-entries-count` meant to be minimised, or is a new, well-covered entry for each new shim healthy (direction `lower` is a guess)?
- Is `proof-lines-per-library-line-permille` a goal (more proof per line of code) or only a size reading? The repository states no ratio.
