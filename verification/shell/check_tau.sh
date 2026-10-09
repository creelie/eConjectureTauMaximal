#!/usr/bin/env bash
# check_tau.sh -- bash integer arithmetic only, for "All tau_k-maximal graphs have the same size".
#   1. Lemma 4.1: G_0 is a-sparse with a(n-1)-1 edges, by enumerating every vertex set,
#      for a = 2, 3 and 2a <= n <= 9.
#   2. The arithmetic of Lemma 4.1 for 2 <= a <= 60: the edge count, (y-1)(2a-y) >= 2 and
#      C(y,2) <= a(y-1)-1 for 2 <= y <= 2a-1, equality at y = 2a, and the two small cases.
#   3. The arithmetic of Lemma 3.1(ii) and of the remark on n <= 2k+1.
# Prints "ALL OK" when everything passes.
set -u
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }

# 1. G_0 by subset enumeration; vertices 0..n-1, A = {0..a-1}, W = {a..2a-1}, w w' = (2a-2, 2a-1)
count=0
for a in 2 3; do
  for ((n = 2 * a; n <= 9; n++)); do
    adj=()
    for ((v = 0; v < n; v++)); do adj[v]=0; done
    m=0
    for ((u = 0; u < n; u++)); do
      for ((v = u + 1; v < n; v++)); do
        if ((u < a || (v < 2 * a && !(u == 2 * a - 2 && v == 2 * a - 1)))); then
          adj[u]=$((adj[u] | 1 << v)); adj[v]=$((adj[v] | 1 << u)); m=$((m + 1))
        fi
      done
    done
    ((m == a * (n - 1) - 1)) || bad "G_0 has $m edges for a=$a n=$n"
    for ((X = 0; X < 1 << n; X++)); do
      s=0; e=0
      for ((v = 0; v < n; v++)); do
        if ((X >> v & 1)); then
          s=$((s + 1)); y=$((adj[v] & X))
          while ((y)); do e=$((e + (y & 1))); y=$((y >> 1)); done
        fi
      done
      e=$((e / 2))
      ((s < 2 || e <= a * (s - 1) - 1)) || bad "G_0 not sparse at a=$a n=$n X=$X"
    done
    count=$((count + 1))
  done
done
((fail == 0)) && ok "G_0 is a-sparse with a(n-1)-1 edges for all $count pairs a in {2,3}, 2a <= n <= 9 (every vertex set)"

# 2. arithmetic of Lemma 4.1
f2=0
for ((a = 2; a <= 60; a++)); do
  for ((n = 2 * a; n <= 2 * a + 40; n++)); do
    ((a * (a - 1) / 2 + a * (n - a) + a * (a - 1) / 2 - 1 == a * (n - 1) - 1)) || f2=1
  done
  for ((y = 2; y <= 2 * a - 1; y++)); do
    (((y - 1) * (2 * a - y) >= 2)) || f2=1
    ((y * (y - 1) / 2 <= a * (y - 1) - 1)) || f2=1
  done
  ((2 * a * (2 * a - 1) / 2 - 1 == a * (2 * a - 1) - 1)) || f2=1
  for ((z = 1; z <= 40; z++)); do
    ((z <= a * z - 1)) || f2=1                         # |Y| = 1: |X| - 1 = z
    ((z < 2 || 0 <= a * (z - 1) - 1)) || f2=1          # Y empty: |X| = z >= 2
  done
done
((f2 == 0)) && ok "Lemma 4.1 arithmetic for 2 <= a <= 60: edge count, (y-1)(2a-y) >= 2, C(y,2) <= a(y-1)-1, small cases" \
            || bad "Lemma 4.1 arithmetic"

# 3. Lemma 3.1(ii): (a(x-1)-1) + (a(y-1)-1) - (a(i-1)-1) = a(x+y-i-1)-1, and the remark
f3=0
for ((a = 2; a <= 12; a++)); do
  for ((x = 2; x <= 15; x++)); do
    for ((y = 2; y <= 15; y++)); do
      for ((i = 2; i <= x && i <= y; i++)); do
        (((a * (x - 1) - 1) + (a * (y - 1) - 1) - (a * (i - 1) - 1) == a * (x + y - i - 1) - 1)) || f3=1
      done
    done
  done
done
for ((k = 1; k <= 60; k++)); do
  for ((x = 2; x <= 2 * k + 1; x++)); do
    ((x * (x - 1) / 2 <= (k + 1) * (x - 1) - 1)) || f3=1
  done
done
((f3 == 0)) && ok "Lemma 3.1(ii) identity, and C(x,2) <= (k+1)(x-1)-1 for 2 <= x <= 2k+1 (k <= 60)" \
            || bad "Lemma 3.1 / remark arithmetic"

if ((fail == 0)); then echo "ALL OK"; else echo "SOME CHECKS FAILED"; fi
exit $fail
