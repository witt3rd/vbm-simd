#!/usr/bin/env bash
# Tier 1 (the pre-landing gate; scripts/land-direct runs it on the rebased combination): the vendored lander is intact, repository lints, forbidden constructs, the Init-only import rule,
# zero-warning build, the axiom gate, the spec-clause gate, the trust ledger. Every gate has a negative self-test and runs it here. Run from the repo root: mise exec -- scripts/tier1.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
t0=$(date +%s)
# RAN-EVIDENCE (docs/decisions/0002-ran-evidence.md): a gate or self-test that never ran must not pass. Every counted gate and test script below runs through `scripts/ran-evidence.sh gate NAME REGEX CMD...`, which
# fails when the command fails, prints no count or prints a zero (a refused tool, a SKIPPED check or a stop by a guard prints none); scripts/test_ran_evidence.sh is the shared negative test.
[ "$(grep -c '^ran_done()' scripts/lib-ran.sh)" = 1 ] && [ "$(grep -c '^must_fail()' scripts/lib-ran.sh)" = 1 ] && [ -x scripts/ran-evidence.sh ] && [ "$(grep -c '^  gate)' scripts/ran-evidence.sh)" = 1 ] || { echo "tier1: scripts/lib-ran.sh or scripts/ran-evidence.sh does not define the ran-evidence mechanism" >&2; exit 1; }
scripts/land/bin/land-check
scripts/lint.sh
scripts/lint-pipefail.sh
scripts/lint-proof-eval.sh --selftest
scripts/ran-evidence.sh gate test_lint_workflows '^ran: test_lint_workflows: ([0-9]+) cases$' scripts/test_lint_workflows.sh
scripts/ran-evidence.sh gate test_ran_evidence '^ran: test_ran_evidence: ([0-9]+) cases$' scripts/test_ran_evidence.sh
python3 scripts/lint-workflows.py
# Long runners (scripts/long-runners.txt) run under scripts/run-scoped.sh (a bounded transient scope, reaped on exit: an aborted run cannot orphan); the lint is negative-tested here (a guard against accidents: indirection is its stated limit).
scripts/lint-scoped-runners.sh --selftest
scripts/ran-evidence.sh gate test_run_scoped '^ran: test_run_scoped: ([0-9]+) cases$' scripts/test_run_scoped.sh
scripts/ran-evidence.sh gate test_reap '^ran: test_reap: ([0-9]+) cases$' scripts/test_reap.sh

# Lean sources under the roots that exist.
lean_sources() { find VbmSimd VbmSimdProofs -name '*.lean'; ls VbmSimd.lean VbmSimdProofs.lean; }

# 1. Forbidden constructs anywhere in Lean sources. Comments may mention them only on lines marked `-- tier1-allow`.
forbidden() { grep -HnE '\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\b' "$@" | grep -v 'tier1-allow' || true; }
bad=$(forbidden $(lean_sources))
if [ -n "$bad" ]; then echo "tier1: forbidden construct(s):" >&2; echo "$bad" >&2; exit 1; fi
st=$(mktemp); trap 'rm -f "$st"' EXIT
for w in sorry admit axiom unsafe implemented_by csimp; do
  echo "theorem t : True := by $w" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: the forbidden-constructs scan does not flag '$w'" >&2; exit 1; }
done
echo "-- a comment that says sorry -- tier1-allow" > "$st"; [ -z "$(forbidden "$st")" ] || { echo "tier1: the tier1-allow marker is not honoured" >&2; exit 1; }
echo "-- a comment that says sorry" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: an unmarked comment is not flagged" >&2; exit 1; }
echo "tier1: forbidden-constructs scan: negative self-tests ok"

# 2. VbmSimd/ imports Init (implicitly) and other VbmSimd modules only: no Std, no Lean, no proofs (a consumer compiles this library into its own artifact).
bad_imports() { grep -HnE '^[[:space:]]*((public|meta|private)[[:space:]]+)*(import|prelude)\b' "$@" | grep -vE ':[0-9]+:import VbmSimd(\.[A-Za-z0-9_]+)*[[:space:]]*$' || true; }
bad=$(bad_imports $(find VbmSimd -name '*.lean') VbmSimd.lean)
if [ -n "$bad" ]; then echo "tier1: VbmSimd may import only VbmSimd modules (Init is implicit):" >&2; echo "$bad" >&2; exit 1; fi
for imp in 'import Lean' 'import Std.Data.HashMap' 'import VbmSimdProofs.Escape' 'prelude' 'public import Lean.Data.Json'; do
  printf '%s\n' "$imp" > "$st"; [ -n "$(bad_imports "$st")" ] || { echo "tier1: the Init-only import scan does not flag: $imp" >&2; exit 1; }
done
printf 'import VbmSimd.Spec\n' > "$st"; [ -z "$(bad_imports "$st")" ] || { echo "tier1: the Init-only import scan flags a VbmSimd import" >&2; exit 1; }
echo "tier1: Init-only import scan: negative self-tests ok"

# 3. Zero-warning build of both libraries (warningAsError is set in lakefile.lean); the mechanism is checked.
# The zero-warning mechanism (scripts/check-zero-warning.sh): the option is set; a file with a warning FAILS with the warning's own diagnostic (a refused or missing lake also fails, with another message: that is not a pass); a clean file passes.
scripts/check-zero-warning.sh
lake build VbmSimd VbmSimdProofs

# 3b. The trusted C shims against their Lean models, and the test's own ability to fail (mutants of the header).
scripts/ran-evidence.sh gate test-shims '^shim-test: ok \(([0-9]+) comparisons' scripts/test-shims.sh

# 4. The axiom gate: every constant of ours depends only on propext, Classical.choice, Quot.sound (--selftest: a non-standard axiom is rejected).
scripts/ran-evidence.sh gate axiom-gate 'axiom gate: ([0-9]+) constants checked' lake env lean --run scripts/AxiomGate.lean --selftest

# 5. The spec clauses, and the trust ledger (docs/trust-ledger.md).
scripts/ran-evidence.sh gate spec-check '^spec-check: ok \(([0-9]+) clauses' scripts/spec-check.sh
scripts/ran-evidence.sh gate trust-ledger '^trust ledger: ([0-9]+) entries' scripts/trust-ledger-check.sh
echo "tier1: ok ($(( $(date +%s) - t0 )) s)"
