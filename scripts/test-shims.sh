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
# Crash probes (the mutants crash on purpose) run through the vendored lander's run-probe: ulimit -c 0 PLUS the dumpable-clear preload, so a crash leaves no core and no crash record (.land/tool/docs/crash-probes.md).
probe="$PWD/.land/tool/bin/run-probe"
"$probe" true || { echo "test-shims: run-probe is refused or unusable: no mutant can be run" >&2; exit 1; }
# The vector bodies must have RUN: on a CPU that has AVX2 (and always on x86-64 CI) the test reports a non-zero number of its AVX2 comparisons, on aarch64 (NEON is baseline there, and CI is the real machine) a non-zero number of its NEON ones;
# a run that skipped them proves nothing about the shim, so it fails. The reports are counted per kernel: the search, the membership masks, the class masks.
vec_ran() {  # vec_ran REQUIRED OUTPUT ISA [WHAT]: fails when comparisons are required and the output says none ran (ISA: AVX2 or NEON; WHAT: "search", the default, "membership masks" or "class masks")
  local n; n=$(sed -n "s/.*; \([0-9][0-9]*\) of them the $3 ${4:-search}.*/\1/p" <<<"$2" | sed -n 1p)
  [ -n "$n" ] || return 1
  [ "$1" != 1 ] || [ "$n" -gt 0 ]
}
vec_ran 1 "shim-test: ok (5 comparisons of the C shims against their Lean models; 3 of them the AVX2 search)" AVX2 || { echo "test-shims: self-test: the ran check rejects a run with AVX2 comparisons" >&2; exit 1; }
! vec_ran 1 "shim-test: ok (5 comparisons of the C shims against their Lean models; 0 of them the AVX2 search)" AVX2 || { echo "test-shims: self-test: the ran check accepts a run with none" >&2; exit 1; }
! vec_ran 0 "shim-test: ok (5 comparisons of the C shims against their Lean models)" AVX2 || { echo "test-shims: self-test: the ran check accepts output with no count" >&2; exit 1; }
vec_ran 1 "shim-test: ok (5 comparisons; 3 of them the AVX2 search; 7 of them the AVX2 membership masks)" AVX2 "membership masks" || { echo "test-shims: self-test: the ran check rejects a run with AVX2 membership comparisons" >&2; exit 1; }
! vec_ran 1 "shim-test: ok (5 comparisons; 3 of them the AVX2 search; 0 of them the AVX2 membership masks)" AVX2 "membership masks" || { echo "test-shims: self-test: the ran check accepts a run with no membership comparisons" >&2; exit 1; }
vec_ran 1 "shim-test: ok (5 comparisons; 3 of them the AVX2 search; 0 of them the NEON search; 4 of them the NEON class masks)" NEON "class masks" || { echo "test-shims: self-test: the ran check rejects a run with NEON class comparisons" >&2; exit 1; }
! vec_ran 1 "shim-test: ok (5 comparisons; 3 of them the AVX2 search; 0 of them the NEON search; 4 of them the NEON class masks)" NEON || { echo "test-shims: self-test: the ran check accepts a run with no NEON search comparisons" >&2; exit 1; }
need_avx2=0; if [ "$(uname -m)" != x86_64 ]; then need_avx2=0; elif [ -n "${CI:-}" ]; then need_avx2=1; elif grep -qw avx2 /proc/cpuinfo 2>/dev/null; then need_avx2=1; fi   # the AVX2 body exists only on x86-64
need_neon=0; if [ "$(uname -m)" = aarch64 ] || [ "$(uname -m)" = arm64 ]; then need_neon=1; fi   # the NEON body exists only on aarch64, where NEON is baseline: always required there
out=$(.lake/build/bin/shim-test); echo "$out"
for w in "search" "membership masks" "class masks"; do
  vec_ran "$need_avx2" "$out" AVX2 "$w" || { echo "test-shims: the AVX2 $w did not run (required on CI and on a CPU with AVX2)" >&2; exit 1; }
  vec_ran "$need_neon" "$out" NEON "$w" || { echo "test-shims: the NEON $w did not run (required on aarch64)" >&2; exit 1; }
done
! grep -q MISMATCH <<<"$out" || { echo "test-shims: the bench's vector and portable results differ" >&2; exit 1; }
# The byte search against unmapped pages (tests/find_guard.c: any read outside the buffer is a SIGSEGV). Built with the toolchain's own compiler, from the include directory it is given.
G=$(mktemp -d); leanc -O2 -I include tests/find_guard.c -o "$G/find_guard" && gout=$("$G/find_guard") && echo "$gout" || { rm -rf "$G"; echo "test-shims: the byte-search guard test failed" >&2; exit 1; }; rm -rf "$G"
[ "$need_neon" = 0 ] || grep -q "neon checked" <<<"$gout" || { echo "test-shims: the guard test did not check the NEON bodies (required on aarch64)" >&2; exit 1; }
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
  "append-shared|s| \&\& lean_is_exclusive(t), 1))|, 1))|"
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
  "class-fast-bound|s|if (lean_sarray_size(out) >= 32) {|if (lean_sarray_size(out) >= 24) {|"
  # the NEON bodies (T15), compiled on aarch64 only. The search: a read past the end, bits kept from before the start, a shift off by one, a dropped member (in the loop, in the tail), no bounds guard, a wrong tail load, a wrong index, the second
  # vector of a step reported as the first, a wrong nibble width, a wrong narrowing shift, a wrong CPU fact. The masks: an over-read, bits kept from before the start, a dropped member, no bounds guard, a wrong tail load, a wrong short-array case,
  # a wrong bit weight, a wrong pairing order. The class masks: an over-read, the low lookup indexed by the high nibble, the low nibble not masked, a wrong shift, a dropped mask, the wrong table half
  "neon-find-overread|s|while (n - i >= 32) {\$|while (n - i >= 17) {|"
  "neon-find-no-shift-out|s|>> (4 \* (16 - (n - i)))|>> 0|"
  "neon-find-shift-off-by-one|s|>> (4 \* (16 - (n - i)))|>> (4 * (15 - (n - i)))|"
  "neon-find-drop-member|s# [\|] (x == c3)##"
  "neon-find-drop-member-tail|s# [\|] (x == vbm_neon_dup((uint8_t)(s >> 24)))##"
  "neon-find-no-bounds|/vbm_simd_find_neon_n/{n;s|  if (i >= n) return n;||}"
  "neon-find-tail-load|s|vbm_simd_members16_neon(p + n - 16, s)|vbm_simd_members16_neon(p + i, s)|"
  "neon-find-index|s|if (m) return i + ((size_t)__builtin_ctzll(m) >> 2); i += 16;|if (m) return i + 1 + ((size_t)__builtin_ctzll(m) >> 2); i += 16;|"
  "neon-find-second-half|s|return i + 16 + ((size_t)__builtin_ctzll(vbm_neon_nib(f)) >> 2)|return i + ((size_t)__builtin_ctzll(vbm_neon_nib(f)) >> 2)|"
  "neon-find-nibble-width|s|return i + ((size_t)__builtin_ctzll(m) >> 2);\$|return i + ((size_t)__builtin_ctzll(m) >> 1);|"
  "neon-nib-shift|s|__builtin_neon_vshrn_n_v((vbm_s16)e, 4, 16)|__builtin_neon_vshrn_n_v((vbm_s16)e, 3, 16)|"
  "neon-has|s|return (uint8_t)VBM_SIMD_NEON; }|return 0; }|"
  "neon-inset-overread|s|if (r >= 64) return vbm_simd_members64_neon(p + i, s);|if (r >= 1) return vbm_simd_members64_neon(p + i, s);|"
  "neon-inset-no-shift-out|s|vbm_simd_members64_neon(p + n - 64, s) >> (64 - r)|vbm_simd_members64_neon(p + n - 64, s) >> 0|"
  "neon-inset-drop-member|s# [\|] (x3 == c3)##"
  "neon-inset-no-bounds|/vbm_simd_inset64_neon_n/{n;s|  if (i >= n) return 0;||}"
  "neon-inset-tail-load|s|vbm_simd_members64_neon(p + n - 64, s)|vbm_simd_members64_neon(p + i, s)|"
  "neon-inset-short-array|s|if (n < 64) return vbm_simd_inset64_scalar(p, n, i, s);||"
  "neon-mask-weights|s|16, 32, 64, 128, 1, 2, 4, 8, 16, 32, 64, 128};|16, 32, 64, 128, 1, 2, 4, 8, 16, 32, 128, 64};|"
  "neon-mask-order|s|t0 = vbm_neon_padd(t0, t1);|t0 = vbm_neon_padd(t1, t0);|"
  "neon-class-overread|s|if (i < n \&\& n - i >= 64) vbm_simd_class_words_neon|if (i < n \&\& n - i >= 1) vbm_simd_class_words_neon|"
  "neon-class-low-index|s|vbm_neon_tbl(lo, x \& nib)|vbm_neon_tbl(lo, x >> 4)|"
  "neon-class-low-unmasked|s|vbm_neon_tbl(lo, x \& nib)|vbm_neon_tbl(lo, x)|"
  "neon-class-shift|s|vbm_neon_tbl(hi, x >> 4)|vbm_neon_tbl(hi, x >> 3)|"
  "neon-class-mask-dropped|s|(c\[3\] \& m) != 0|(c[2] \& m) != 0|"
  "neon-class-table-half|s|hi = vbm_neon_ld16(t + 16)|hi = vbm_neon_ld16(t)|"
)
# The NEON bodies (neon-*) exist only on aarch64 (#elif __aarch64__ in the header): on any other machine those mutants edit code that is not compiled, so they are not run there (the arm64 job runs them).
# The AVX2 body (find-overread .. find-index, inset-overread .. inset-short-array, class-overread .. class-half-shift) exists only on x86-64 (#if __x86_64__ in the header): on any other machine those mutants edit code that is not compiled, so they are not run there (the x86-64 job runs them).
if [ "$(uname -m)" = x86_64 ]; then kept=(); for m in "${mutants[@]}"; do case ${m%%|*} in neon-*) ;; *) kept+=("$m");; esac; done; mutants=("${kept[@]}"); fi
if [ "$(uname -m)" != x86_64 ]; then kept=(); for m in "${mutants[@]}"; do case ${m%%|*} in neon-*|find-scalar-*|inset-scalar-*|append-*|class-scalar-*|class-shared*|class-partial-store|class-fast-bound|ld64-*|st64-*|st32-*|ctz-*) kept+=("$m");; esac; done; mutants=("${kept[@]}"); fi
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
  export SHIM_TEST_NO_BENCH=1   # a mutant run needs the comparisons only, not the bench
  ( cd "$d" && "$probe" .lake/build/bin/shim-test >/dev/null 2>&1 ) || rc=$?
  [ "$rc" != 2 ] || { echo "test-shims: mutant $name: run-probe refused" >&2; return 2; }
  if [ "$rc" = 0 ]; then ( cd "$d" && "$probe" ./find_guard >/dev/null 2>&1 ) || rc=$?; [ "$rc" != 2 ] || { echo "test-shims: mutant $name: run-probe refused" >&2; return 2; }; fi
  [ "$rc" != 0 ] || { echo "test-shims: the test did NOT catch mutant $name" >&2; return 1; }
}
for m in "${mutants[@]}"; do set -m; run_mutant "$m" & pids+=($!); set +m; done
bad=0; for p in "${pids[@]}"; do wait "$p" || bad=1; done
[ "$bad" = 0 ] || exit 1
echo "test-shims: ok (${#mutants[@]} mutants of the header, each caught)"
