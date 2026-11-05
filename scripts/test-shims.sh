#!/usr/bin/env bash
# Tier 1: the trusted C shims (include/vbm_simd.h) against their Lean models (tests/ShimTest.lean, built as `shim-test`), and the test's own ability to fail: each of several hand-made MUTANTS of
# the header (a wrong offset, a missing copy-on-share, a wrong zero case, a skipped partial store) is built in a scratch copy and must be caught by the same test.
# Lake does not track the header as an input of the C it compiles, so the compiled objects of the test are deleted first: a header edit always rebuilds.
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."
# Scoped (scripts/run-scoped.sh, scripts/long-runners.txt): re-exec under a bounded transient scope, so an aborted run cannot orphan its builds.
[ -n "${RUN_SCOPED_INNER:-}" ] || RUN_SCOPED_INNER=1 exec scripts/run-scoped.sh test-shims 1800 "$PWD/scripts/test-shims.sh" "$@"
ulimit -c 0   # a mutant may crash on purpose: no core file
stale() { rm -f "$1"/.lake/build/ir/ShimTest.c.o.* "$1"/.lake/build/ir/VbmSimd/*.c.o.* "$1"/.lake/build/ir/VbmSimd.c.o.* "$1"/.lake/build/bin/shim-test 2>/dev/null || true; }
stale .
lake build shim-test
.lake/build/bin/shim-test
# The byte search against unmapped pages (tests/find_guard.c: any read outside the buffer is a SIGSEGV). Built with the toolchain's own compiler, from the include directory it is given.
G=$(mktemp -d); leanc -O2 -I include tests/find_guard.c -o "$G/find_guard" && "$G/find_guard" || { rm -rf "$G"; echo "test-shims: the byte-search guard test failed" >&2; exit 1; }; rm -rf "$G"
. scripts/lib-reap.sh   # an abort or exit stops the mutant jobs by the pids held here (each job is its own process group: set -m); never by pattern
pids=(); T=$(mktemp -d); trap 'reap_pids "${pids[@]}"; rm -rf "$T"' EXIT; trap 'exit 143' INT TERM HUP
# mutant NAME 'sed expression'
mutants=(
  "ld64-offset|s|__builtin_memcpy(&w, p + i, 8)|__builtin_memcpy(\&w, p + i + 1, 8)|"
  "ld64-tail-shift|s|w \|= (uint64_t)p\[i + j\] << (8 \* j)|w \|= (uint64_t)p[i + j] << (8 * j + 1)|"
  "st64-no-copy|0,/lean_object \*r = lean_sarray_ensure_exclusive(out);/s||lean_object *r = out;|"
  "st64-skip-partial|s|if (k < (n + 7) / 8) {|if (k < n / 8) {|"
  "st32-skip-partial|s|if (k < (n + 3) / 4) {|if (k < n / 4) {|"
  "ctz-zero|s|: 64; }|: 63; }|"
  # the byte search (T11): a read past the end, a tail that keeps bytes before the start, a shift off by one, a dropped member, no bounds guard, a wrong tail load, a wrong index, the scalar loop, the CPU test
  "find-overread|s|while (n - i >= 32)|while (n - i >= 1)|"
  "find-no-shift-out|s|>> (32 - (n - i))|>> 0|"
  "find-shift-off-by-one|s|>> (32 - (n - i))|>> (31 - (n - i))|"
  "find-drop-member|s# [\|] (x == z + (signed char)(s >> 24))##"
  "find-no-bounds|s|  if (i >= n) return n;||"
  "find-tail-load|s|vbm_simd_members32(p + n - 32, s)|vbm_simd_members32(p + i, s)|"
  "find-index|s|return i + (size_t)__builtin_ctz(m); i += 32;|return i + 1 + (size_t)__builtin_ctz(m); i += 32;|"
  "find-scalar-member|s# [\|][\|] p\[i\] == b3##"
  "find-scalar-start|s|for (; i < n; i++) if|for (i = 0; i < n; i++) if|"
  "cpu-bit|s|c = (b >> 5) \& 1|c = (b >> 6) \& 1|"
)
run_mutant() {
  local name=${1%%|*} expr=${1#*|}; local d=$T/$name
  mkdir -p "$d"; cp -r include tests lakefile.lean lean-toolchain VbmSimd VbmSimd.lean "$d"/ 2>/dev/null; cp -r .lake "$d"/.lake; rm -rf "$d"/.lake/config "$d"/.lake/lakefile.olean* "$d"/.lake/lakefile.olean.* 2>/dev/null || true   # the configured lakefile bakes in the header path (__dir__): reconfigure in the copy
  sed -i -e "$expr" "$d/include/vbm_simd.h"
  if cmp -s include/vbm_simd.h "$d/include/vbm_simd.h"; then echo "test-shims: mutant $name did not change the header" >&2; return 2; fi
  stale "$d"
  ( cd "$d" && lake build shim-test >/dev/null 2>"$d/build.err" ) || { echo "test-shims: mutant $name does not build: $(tail -3 "$d/build.err")" >&2; return 2; }
  leanc -O2 -I "$d/include" "$d/tests/find_guard.c" -o "$d/find_guard" 2>"$d/build.err" || { echo "test-shims: mutant $name does not build (guard test): $(tail -3 "$d/build.err")" >&2; return 2; }
  # caught = the Lean shim test fails or the guard test fails (a crash on a guard page included)
  if ( cd "$d" && .lake/build/bin/shim-test >/dev/null 2>&1 && ./find_guard >/dev/null 2>&1 ); then echo "test-shims: the test did NOT catch mutant $name" >&2; return 1; fi
}
for m in "${mutants[@]}"; do set -m; run_mutant "$m" & pids+=($!); set +m; done
bad=0; for p in "${pids[@]}"; do wait "$p" || bad=1; done
[ "$bad" = 0 ] || exit 1
echo "test-shims: ok (${#mutants[@]} mutants of the header, each caught)"
