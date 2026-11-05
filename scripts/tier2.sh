#!/usr/bin/env bash
# Tier 2 (assurance, the SLOW checks; CI runs it on a schedule and on dispatch; it never gates a landing):
#  1. Tier 1 again.
#  2. `leanchecker --fresh` replays every declaration of both libraries in a fresh environment (guards a tampered or stale .olean).
#  3. nanoda, an independent kernel implementation shipped in the Lean release, re-checks the exported proofs.
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN_PREFIX=$(lean --print-prefix)
scripts/tier1.sh
echo "tier2: leanchecker --fresh VbmSimd"
lake env "$LEAN_PREFIX/bin/leanchecker" --fresh VbmSimd
echo "tier2: leanchecker --fresh VbmSimdProofs"
lake env "$LEAN_PREFIX/bin/leanchecker" --fresh VbmSimdProofs
echo "tier2: external checker (nanoda) over the exported proofs"
exp=$(mktemp); cfg=$(mktemp)
trap 'rm -f "$exp" "$cfg"' EXIT
lake env "$LEAN_PREFIX/bin/leanexport" VbmSimd VbmSimdProofs > "$exp"
cat > "$cfg" <<JSON
{"export_file_path":"$exp","permitted_axioms":["propext","Classical.choice","Quot.sound"],"unpermitted_axiom_hard_error":false,"nat_extension":true,"string_extension":true,"print_success_message":true}
JSON
out=$("$LEAN_PREFIX/bin/nanoda_bin" "$cfg" 2>&1) || { echo "$out"; exit 1; }
grep -q "with no typechecker errors" <<<"$out" || { echo "$out"; exit 1; }
sed -n 1p <<<"$out"
echo "tier2: ok"
