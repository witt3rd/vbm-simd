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
# Crash probes (the mutants crash on purpose) run through the vendored lander's run-probe: ulimit -c 0 PLUS the dumpable-clear preload, so a crash leaves no core and no crash record (scripts/land/docs/crash-probes.md).
probe="$PWD/scripts/land/bin/run-probe"
"$probe" true || { echo "test-shims: run-probe is refused or unusable: no mutant can be run" >&2; exit 1; }
# The AVX2 search must have RUN: on a CPU that has AVX2 (and always on x86-64 CI; aarch64 has no AVX2 body, the portable path runs) the test reports a non-zero number of its comparisons; a run that skipped them proves nothing about the shim.
avx2_ran() {  # avx2_ran REQUIRED OUTPUT [WHAT]: fails when AVX2 comparisons are required and the output says none ran (WHAT: "search", the default, or "membership masks")
  local n; n=$(sed -n "s/.*; \([0-9][0-9]*\) of them the AVX2 ${3:-search}.*/\1/p" <<<"$2" | sed -n 1p)
  [ -n "$n" ] || return 1
  [ "$1" != 1 ] || [ "$n" -gt 0 ]
}
avx2_ran 1 "shim-test: ok (5 comparisons of the C shims against their Lean models; 3 of them the AVX2 search)" || { echo "test-shims: self-test: the AVX2-ran check rejects a run with AVX2 comparisons" >&2; exit 1; }
! avx2_ran 1 "shim-test: ok (5 comparisons of the C shims against their Lean models; 0 of them the AVX2 search)" || { echo "test-shims: self-test: the AVX2-ran check accepts a run with none" >&2; exit 1; }
! avx2_ran 0 "shim-test: ok (5 comparisons of the C shims against their Lean models)" || { echo "test-shims: self-test: the AVX2-ran check accepts output with no count" >&2; exit 1; }
need_avx2=0; if [ "$(uname -m)" != x86_64 ]; then need_avx2=0; elif [ -n "${CI:-}" ]; then need_avx2=1; elif grep -qw avx2 /proc/cpuinfo 2>/dev/null; then need_avx2=1; fi   # the AVX2 body exists only on x86-64; on aarch64 the portable path is the one that runs
out=$(.lake/build/bin/shim-test); echo "$out"
avx2_ran "$need_avx2" "$out" || { echo "test-shims: the AVX2 search did not run (required on CI and on a CPU with AVX2)" >&2; exit 1; }
avx2_ran "$need_avx2" "$out" "membership masks" || { echo "test-shims: the AVX2 membership masks did not run (required on CI and on a CPU with AVX2)" >&2; exit 1; }
avx2_ran 1 "shim-test: ok (5 comparisons; 3 of them the AVX2 search; 7 of them the AVX2 membership masks)" "membership masks" || { echo "test-shims: self-test: the AVX2-ran check rejects a run with AVX2 membership comparisons" >&2; exit 1; }
! avx2_ran 1 "shim-test: ok (5 comparisons; 3 of them the AVX2 search; 0 of them the AVX2 membership masks)" "membership masks" || { echo "test-shims: self-test: the AVX2-ran check accepts a run with no membership comparisons" >&2; exit 1; }
avx2_ran "$need_avx2" "$out" "class masks" || { echo "test-shims: the AVX2 class masks did not run (required on CI and on a CPU with AVX2)" >&2; exit 1; }
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
  # the membership masks (T12): a read past the end, bits kept from before the start, a dropped member, no bounds guard, a wrong tail load, a wrong short-array case, a scalar loop that ignores the start
  "inset-overread|s|if (r >= 64) return vbm_simd_members64(p + i, s);|if (r >= 1) return vbm_simd_members64(p + i, s);|"
  "inset-no-shift-out|s|>> (64 - r)|>> 0|"
  "inset-drop-member|s# [\|] (x1 == c3)##"
  "inset-no-bounds|/vbm_simd_inset64_avx2_n/{n;s|  if (i >= n) return 0;||}"
  "inset-tail-load|s|vbm_simd_members64(p + n - 64, s)|vbm_simd_members64(p + i, s)|"
  "inset-short-array|s|if (n < 64) return vbm_simd_inset64_scalar(p, n, i, s);||"
  "inset-scalar-start|s|j < 64 \&\& j < n - i|j < 64 \&\& j < n|"
  # the short append (T13): no check for room in the destination, no check that the run is inside the source, a longer limit than the moves cover, a wrong offset of the second store (a write past the run), of the second load, a move
  # of seven bytes as eight (a read before the run), an append into a shared array, a size one too large, a size not updated
  "append-room|s| \&\& n <= tc - ts||"
  "append-source|s| \&\& n <= as - i;|;|"
  "append-limit|s|return n <= 32 \&\&|return n <= 33 \&\&|"
  "append-store-tail|s|__builtin_memcpy(d + n - 8, \&y, 8)|__builtin_memcpy(d + n - 7, \&y, 8)|"
  "append-load-tail|s|__builtin_memcpy(\&y, s + n - 4, 4)|__builtin_memcpy(\&y, s + n - 3, 4)|"
  "append-seven|s|else if (n >= 8) { uint64_t x, y;|else if (n >= 7) { uint64_t x, y;|"
  "append-sixteen|s|if (n >= 16) {|if (n >= 15) {|"
  "append-sixteen-tail|s|__builtin_memcpy(d + n - 16, \&y0, 8)|__builtin_memcpy(d + n - 15, \&y0, 8)|"
  "append-shared|s| \&\& lean_is_exclusive(t))|)|"
  "append-size-plus|s|lean_sarray_set_size(t, ts + n)|lean_sarray_set_size(t, ts + n + 1)|"
  "append-no-size|/lean_sarray_set_size(t, ts + n);/d"
  # the class masks (T14): a read past the end, the low-nibble lookup indexed by the high nibble, a wrong high-nibble shift, a mask word dropped (the fourth mask is the third), a missing inversion, the second half not shifted into place,
  # the scalar table's high lookup without its offset, a store into a shared destination, a store of a word that does not wholly fit
  "class-overread|s|if (i < n \&\& n - i >= 64) vbm_simd_class_words_avx2|if (i < n \&\& n - i >= 1) vbm_simd_class_words_avx2|"
  "class-low-index|s|__builtin_ia32_pshufb256(lo, x \& nib)|__builtin_ia32_pshufb256(lo, xh \& nib)|"
  "class-shift|s|(vbm_w16)x >> 4)|(vbm_w16)x >> 3)|"
  "class-mask-dropped|s|(c \& m3) == z|(c \& m2) == z|"
  "class-no-invert|s|(uint64_t)(uint32_t)~e0 <<|(uint64_t)(uint32_t)e0 <<|"
  "class-half-shift|s|~e2 << (32 \* h)|~e2 << 0|"
  "class-scalar-high|s|t\[16 + (v >> 4)\] \& m)|t[(v >> 4)] \& m)|"
  "class-shared|/vbm_simd_put4(lean_obj_arg/,/^}/s|lean_sarray_ensure_exclusive(out)|out|"
  "class-shared-slow|/vbm_simd_put4_slow/,/^}/s|lean_sarray_ensure_exclusive(out)|out|"
  "class-partial-store|/vbm_simd_put4_slow/,/^}/s|8 \* k + 8 <= n|8 * k < n|"
  "class-fast-bound|s|if (lean_sarray_size(out) >= 32) {|if (lean_sarray_size(out) >= 24) {|"
)
# The AVX2 body (find-overread .. find-index, inset-overread .. inset-short-array, class-overread .. class-half-shift) exists only on x86-64 (#if __x86_64__ in the header): on any other machine those mutants edit code that is not compiled, so they are not run there (the x86-64 job runs them).
if [ "$(uname -m)" != x86_64 ]; then kept=(); for m in "${mutants[@]}"; do case ${m%%|*} in find-scalar-*|inset-scalar-*|append-*|class-scalar-*|class-shared*|class-partial-store|class-fast-bound|ld64-*|st64-*|st32-*|ctz-*) kept+=("$m");; esac; done; mutants=("${kept[@]}"); fi
run_mutant() {
  local name=${1%%|*} expr=${1#*|}; local d=$T/$name
  mkdir -p "$d"; cp -r include tests lakefile.lean lean-toolchain VbmSimd VbmSimd.lean "$d"/ 2>/dev/null; cp -r .lake "$d"/.lake; rm -rf "$d"/.lake/config "$d"/.lake/lakefile.olean* "$d"/.lake/lakefile.olean.* 2>/dev/null || true   # the configured lakefile bakes in the header path (__dir__): reconfigure in the copy
  sed -i -e "$expr" "$d/include/vbm_simd.h"
  if cmp -s include/vbm_simd.h "$d/include/vbm_simd.h"; then echo "test-shims: mutant $name did not change the header" >&2; return 2; fi
  stale "$d"
  ( cd "$d" && lake build shim-test >/dev/null 2>"$d/build.err" ) || { echo "test-shims: mutant $name does not build: $(tail -3 "$d/build.err")" >&2; return 2; }
  leanc -O2 -I "$d/include" "$d/tests/find_guard.c" -o "$d/find_guard" 2>"$d/build.err" || { echo "test-shims: mutant $name does not build (guard test): $(tail -3 "$d/build.err")" >&2; return 2; }
  # caught = the Lean shim test fails or the guard test fails (a crash on a guard page included), both under run-probe (no core, no crash record); exit 2 is run-probe refusing, not a catch
  local rc=0
  ( cd "$d" && "$probe" .lake/build/bin/shim-test >/dev/null 2>&1 ) || rc=$?
  [ "$rc" != 2 ] || { echo "test-shims: mutant $name: run-probe refused" >&2; return 2; }
  if [ "$rc" = 0 ]; then ( cd "$d" && "$probe" ./find_guard >/dev/null 2>&1 ) || rc=$?; [ "$rc" != 2 ] || { echo "test-shims: mutant $name: run-probe refused" >&2; return 2; }; fi
  [ "$rc" != 0 ] || { echo "test-shims: the test did NOT catch mutant $name" >&2; return 1; }
}
for m in "${mutants[@]}"; do set -m; run_mutant "$m" & pids+=($!); set +m; done
bad=0; for p in "${pids[@]}"; do wait "$p" || bad=1; done
[ "$bad" = 0 ] || exit 1
echo "test-shims: ok (${#mutants[@]} mutants of the header, each caught)"
