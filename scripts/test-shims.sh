#!/usr/bin/env bash
# Tier 1: the trusted C shims (include/vbm_simd.h) against their Lean models (tests/ShimTest.lean, built as `shim-test`), and the test's own ability to fail: each of several hand-made MUTANTS of
# the header (a wrong offset, a missing copy-on-share, a wrong zero case, a skipped partial store) is built in a scratch copy and must be caught by the same test.
# Lake does not track the header as an input of the C it compiles, so the compiled objects of the test are deleted first: a header edit always rebuilds.
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."
ulimit -c 0   # a mutant may crash on purpose: no core file
stale() { rm -f "$1"/.lake/build/ir/ShimTest.c.o.* "$1"/.lake/build/ir/VbmSimd/*.c.o.* "$1"/.lake/build/ir/VbmSimd.c.o.* "$1"/.lake/build/bin/shim-test 2>/dev/null || true; }
stale .
lake build shim-test >/dev/null
.lake/build/bin/shim-test
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
# mutant NAME 'sed expression'
mutants=(
  "ld64-offset|s|__builtin_memcpy(&w, p + i, 8)|__builtin_memcpy(\&w, p + i + 1, 8)|"
  "ld64-tail-shift|s|w \|= (uint64_t)p\[i + j\] << (8 \* j)|w \|= (uint64_t)p[i + j] << (8 * j + 1)|"
  "st64-no-copy|0,/lean_object \*r = lean_sarray_ensure_exclusive(out);/s||lean_object *r = out;|"
  "st64-skip-partial|s|if (k < (n + 7) / 8) {|if (k < n / 8) {|"
  "st32-skip-partial|s|if (k < (n + 3) / 4) {|if (k < n / 4) {|"
  "ctz-zero|s|: 64; }|: 63; }|"
)
run_mutant() {
  local name=${1%%|*} expr=${1#*|}; local d=$T/$name
  mkdir -p "$d"; cp -r include tests lakefile.lean lean-toolchain VbmSimd VbmSimd.lean "$d"/ 2>/dev/null; cp -r .lake "$d"/.lake
  sed -i -e "$expr" "$d/include/vbm_simd.h"
  if cmp -s include/vbm_simd.h "$d/include/vbm_simd.h"; then echo "test-shims: mutant $name did not change the header" >&2; return 2; fi
  stale "$d"
  ( cd "$d" && lake build shim-test >/dev/null 2>"$d/build.err" ) || { echo "test-shims: mutant $name does not build: $(tail -3 "$d/build.err")" >&2; return 2; }
  if ( cd "$d" && .lake/build/bin/shim-test >/dev/null 2>&1 ); then echo "test-shims: the test did NOT catch mutant $name" >&2; return 1; fi
}
pids=(); for m in "${mutants[@]}"; do run_mutant "$m" & pids+=($!); done
bad=0; for p in "${pids[@]}"; do wait "$p" || bad=1; done
[ "$bad" = 0 ] || exit 1
echo "test-shims: ok (${#mutants[@]} mutants of the header, each caught)"
