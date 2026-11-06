#!/usr/bin/env bash
# Tier 1 (the landing check): build, the guards that ARE the verified product, and the real tests. Nothing else refuses a landing.
#   guards: no sorry/axiom/unsafe in Lean sources; Init-only imports; a warning-free build; the trusted C shims agree with their Lean models; only the standard axioms; every spec clause has its proof; a new trusted boundary has a trust-ledger entry.
# Run from the repo root: mise exec -- scripts/tier1.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
lean_sources() { find VbmSimd VbmSimdProofs -name '*.lean'; ls VbmSimd.lean VbmSimdProofs.lean; }
# 1. Forbidden constructs in Lean sources; a comment may mention one only on a line marked `-- tier1-allow`.
bad=$(grep -HnE '\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\b' $(lean_sources) | grep -v 'tier1-allow' || true)
if [ -n "$bad" ]; then echo "tier1: forbidden construct(s):" >&2; echo "$bad" >&2; exit 1; fi
# 2. VbmSimd imports Init (implicit) and its own modules only.
bad=$(grep -HnE '^[[:space:]]*((public|meta|private)[[:space:]]+)*(import|prelude)\b' $(find VbmSimd -name '*.lean') VbmSimd.lean | grep -vE ':[0-9]+:import VbmSimd(\.[A-Za-z0-9_]+)*[[:space:]]*$' || true)
if [ -n "$bad" ]; then echo "tier1: VbmSimd may import only VbmSimd modules:" >&2; echo "$bad" >&2; exit 1; fi
# 3. Build both libraries (warningAsError is set in lakefile.lean).
lake build VbmSimd VbmSimdProofs
# 3b. The trusted C shims against their Lean models (and mutants of the header).
scripts/test-shims.sh
# 4. Only the standard axioms. 5. Every spec clause has its proof; a new trusted boundary has a trust-ledger entry.
lake env lean --run scripts/AxiomGate.lean
scripts/spec-check.sh
scripts/trust-ledger-check.sh
echo "tier1: ok"
