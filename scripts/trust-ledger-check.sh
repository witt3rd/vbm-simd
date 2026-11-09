#!/usr/bin/env bash
# Tier 1: the trust ledger (docs/trust-ledger.md) names everything outside our direct control that vbm-simd executes or depends on. The REQUIRED set is derived from the tree, not from the
# ledger: every @[extern] symbol in the Lean sources, every C header under include/, the build pins, the vendored lander's pin, the pieces the Lean pin brings (compiler,
# runtime, bundled clang/ld.lld), and the tools the scripts call. A new boundary with no entry FAILS; an entry covering nothing required FAILS. The checker (scripts/trust_ledger.py)
# negative-self-tests itself on every run: remove any entry and it must fail. Prints `trust ledger: N entries ...`.
# Usage: scripts/trust-ledger-check.sh [ledger]
set -euo pipefail
cd "$(dirname "$0")/.."
ledger=${1:-docs/trust-ledger.md}
req=$(mktemp); trap 'rm -f "$req"' EXIT
files() { git ls-files --cached --others --exclude-standard "$@"; }   # a file not yet added is still required
{
  { files 'include/*.h' 'include/**/*.h' lean-toolchain mise.toml lakefile.lean scripts/land/PIN; } | sed 's/^/file:/'
  # every FFI symbol declared in Lean (an unnamed one needs a key too)
  grep -rhE '^[[:space:]]*@\[extern' VbmSimd --include='*.lean' 2>/dev/null | sed -E 's/.*@\[extern[^"]*"([^"]+)".*/extern:\1/; t; s/.*/extern:UNNAMED/' | sort -u || true
  # what the Lean pin brings: the compiler (frontend, kernel, C emitter), the runtime (lean.h, libleanrt), the bundled clang and ld.lld
  printf '%s\n' lean-compiler lean-runtime clang-lld
  # tools run as processes: a fixed watch-list found in scripts/ and the build file
  [ -f scripts/trust_ledger.py ] && echo tool:python3 || true   # the checker itself (excluded from the grep below: it names every watch-listed tool)
  for t in git gh mise flock lake leanchecker nanoda; do
    files scripts lakefile.lean | grep -v -e 'scripts/trust' | xargs grep -lw -- "$t" >/dev/null 2>&1 && echo "tool:$t" || true; done
} | sort -u > "$req"
python3 scripts/trust_ledger.py "$ledger" "$req"
