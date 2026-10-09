#!/usr/bin/env bash
# run_all.sh -- re-run every check of "All tau_k-maximal graphs have the same size".
#
#   C       verification/c/taumax.c           every labelled graph on n <= 7 vertices, k = 1, 2, 3:
#                                             Lemma 2.1, Theorem 1.1, isomorphism classes
#   C++     verification/cpp/taumax.cpp       Lemma 2.1 on random graphs (partition formula), greedy
#                                             growth, Lemma 4.1 for a <= 6, n <= 16
#   Shell   verification/shell/check_tau.sh   bash integer arithmetic only
#   Python  verification/python/verify_tau.py every labelled graph on n <= 6 vertices, by
#                                             spanning-tree enumeration
#   Julia   verification/julia/verify_tau.jl  the pebble game of Lee and Streinu (if julia is on PATH
#                                             or $JULIA is set)
#   Lean    verification/lean/TauMaximal.lean (if lean is on PATH; the folder pins v4.34.1)
#           verification/lean/mathlib         (MATHLIB=1 only: lake fetches Mathlib's cache and builds
#                                             the proof of Lemmas 3.1, 3.2, 4.1 and Theorem 1.1 in
#                                             sparse form for every n and k)
#
# Exit status 0 means every check that ran passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
V="$ROOT/verification"
BUILD="$ROOT/build"
mkdir -p "$BUILD"
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }
ok() { echo "ok:   $*"; }

echo "== C and C++"
cc -O2 -Wall -o "$BUILD/taumax" "$V/c/taumax.c" || fail "compile taumax.c"
c++ -O2 -Wall -std=c++17 -o "$BUILD/taumax_cpp" "$V/cpp/taumax.cpp" || fail "compile taumax.cpp"
"$BUILD/taumax" > "$BUILD/c.txt" && grep -q '^ALL OK' "$BUILD/c.txt" \
  && grep -q "k=1 n=7: 70 isomorphism classes" "$BUILD/c.txt" \
  && ok "C: all labelled graphs on n <= 7 vertices (190491 tau_1-maximal on 7, 70 classes)" \
  || fail "C (see build/c.txt)"
"$BUILD/taumax_cpp" > "$BUILD/cpp.txt" && grep -q '^ALL OK' "$BUILD/cpp.txt" \
  && ok "C++: partition formula, greedy growth, G_0" || fail "C++ (see build/cpp.txt)"

echo "== Shell"
bash "$V/shell/check_tau.sh" > "$BUILD/sh.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/sh.txt" \
  && ok "check_tau.sh" || fail "check_tau.sh (see build/sh.txt)"

echo "== Python"
python3 "$V/python/verify_tau.py" > "$BUILD/py.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/py.txt" \
  && ok "verify_tau.py" || fail "verify_tau.py (see build/py.txt)"

echo "== Julia"
JULIA="${JULIA:-$(command -v julia || true)}"
if [ -z "$JULIA" ]; then echo "julia not found: skipping"; else
  "$JULIA" "$V/julia/verify_tau.jl" > "$BUILD/jl.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/jl.txt" \
    && ok "verify_tau.jl" || fail "verify_tau.jl (see build/jl.txt)"
fi

echo "== Lean"
if ! command -v lean > /dev/null; then echo "lean not found: skipping (install elan)"; else
  out=$(cd "$V/lean" && lean TauMaximal.lean 2>&1); st=$?
  echo "$out" > "$BUILD/lean.txt"
  if [ $st -eq 0 ] && ! grep -q "error\|sorryAx" <<< "$out" \
       && grep -q "'exhaustive' depends on axioms: \[propext\]" <<< "$out" \
       && grep -q "'example_small' depends on axioms: \[propext\]" <<< "$out"; then
    ok "TauMaximal.lean (kernel-checked)"
  else fail "TauMaximal.lean (see build/lean.txt)"; fi
  if [ "${MATHLIB:-0}" = 1 ]; then
    out=$(cd "$V/lean/mathlib" && lake exe cache get > /dev/null && lake build 2>&1); st=$?
    echo "$out" > "$BUILD/lean_mathlib.txt"
    if [ $st -eq 0 ] && ! grep -q "sorryAx\|error" <<< "$out" \
         && [ "$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" <<< "$out")" = 2 ]; then
      ok "mathlib/TauMaximalMathlib.lean (every n and k; standard axioms only)"
    else fail "mathlib/TauMaximalMathlib.lean (see build/lean_mathlib.txt)"; fi
  else echo "Mathlib proof skipped (set MATHLIB=1)"; fi
fi

if [ $FAILED -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $FAILED
