/*
 * taumax.c -- exhaustive check of Theorem 1.1 and Lemma 2.1 of
 * "All tau_k-maximal graphs have the same size" on every labelled graph with n <= 7 vertices.
 *
 * Write a = k + 1. For an edge set m of K_n (a bit mask over the n(n-1)/2 pairs), we decide
 * whether taubar(m) >= a directly from the definition, without the Nash-Williams--Tutte theorem:
 * if every m - e has taubar < a but m has taubar >= a, a witness X spans a edge-disjoint spanning
 * trees using every edge of m, so m is exactly a union of a edge-disjoint spanning trees of the
 * vertices it touches. We test that by backtracking over colourings of the edges in which every
 * colour class is a forest. Processing the masks in increasing order gives taubar(m) <= k for all m.
 *
 * Then, for every m:
 *   Lemma 2.1:   taubar(m) <= k  <=>  e(X) <= a(|X|-1)-1 for all |X| >= 2;
 *   Theorem 1.1: m is tau_k-maximal  <=>  m is a-sparse with a(n-1)-1 edges (for n >= 2a),
 *                and K_n is the only tau_k-maximal graph for n < 2a.
 * The tau_k-maximal graphs are also sorted into isomorphism classes (orbits under the n!
 * relabellings); for k = 1 the numbers of classes, 1, 3, 13, 70 for n = 4..7, are the numbers of
 * minimally rigid (Laman) graphs in OEIS A227117.
 *
 * Usage: taumax          (k = 1: n = 2..7; k = 2: n = 2..7; k = 3: n = 2..7)
 * Prints "ALL OK" when every check passes.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int n, a, M;
static int eu[32], ev[32];
static uint32_t inX[256];   /* edges inside each vertex set */

/* backtracking: colour edges idx..cnt-1 so that each colour class stays a forest */
static int ecol_u[32], ecol_v[32], cnt;
static int comp[8][32][8];  /* comp[colour][depth][vertex] */

static int find_label(const int *c, int v) { return c[v]; }

static int colour(int idx, int used) {
  if (idx == cnt) return 1;
  int u = ecol_u[idx], v = ecol_v[idx];
  int lim = used < a ? used + 1 : a;  /* symmetry: a new colour only as the next unused one */
  for (int c = 0; c < lim; c++) {
    int *cur = comp[c][idx];
    int lu = find_label(cur, u), lv = find_label(cur, v);
    if (lu == lv) continue;           /* would close a cycle in colour c */
    /* copy all colours' labels to depth idx+1, merging in colour c */
    for (int d = 0; d < a; d++)
      for (int x = 0; x < n; x++) {
        int y = comp[d][idx][x];
        comp[d][idx + 1][x] = (d == c && y == lv) ? lu : y;
      }
    if (colour(idx + 1, c + 1 > used ? c + 1 : used)) return 1;
  }
  return 0;
}

/* is m the union of a edge-disjoint spanning trees of the vertices it touches? */
static int decomposes(uint32_t m, int nv) {
  if (__builtin_popcount(m) != a * (nv - 1)) return 0;
  cnt = 0;
  for (int e = 0; e < M; e++)
    if (m >> e & 1) { ecol_u[cnt] = eu[e]; ecol_v[cnt] = ev[e]; cnt++; }
  for (int d = 0; d < a; d++)
    for (int x = 0; x < n; x++) comp[d][0][x] = x;
  /* each colour class is a forest with nv-1 edges on nv vertices: a spanning tree */
  return colour(0, 0);
}

static int sparse(uint32_t m) {
  for (int X = 0; X < (1 << n); X++) {
    int s = __builtin_popcount(X);
    if (s < 2) continue;
    if (__builtin_popcount(m & inX[X]) > a * (s - 1) - 1) return 0;
  }
  return 1;
}

/* number of orbits of the maximal graphs under relabelling, checking that the set is invariant */
static int perm[8], usedv[8], nperm;
static int (*perms)[8];
static void gen(int i) {
  if (i == n) { for (int j = 0; j < n; j++) perms[nperm][j] = perm[j]; nperm++; return; }
  for (int v = 0; v < n; v++)
    if (!usedv[v]) { usedv[v] = 1; perm[i] = v; gen(i + 1); usedv[v] = 0; }
}
static long classes(const unsigned char *isMax, uint32_t N, int *invariant) {
  int fact = 1;
  for (int i = 2; i <= n; i++) fact *= i;
  perms = malloc(sizeof(int[8]) * fact);
  nperm = 0;
  gen(0);
  int eidx[8][8];
  for (int e = 0; e < M; e++) { eidx[eu[e]][ev[e]] = e; eidx[ev[e]][eu[e]] = e; }
  unsigned char *seen = calloc(N, 1);
  long c = 0;
  *invariant = 1;
  for (uint32_t m = 0; m < N; m++) {
    if (!isMax[m] || seen[m]) continue;
    c++;
    for (int p = 0; p < nperm; p++) {
      uint32_t im = 0;
      for (int e = 0; e < M; e++)
        if (m >> e & 1) im |= 1u << eidx[perms[p][eu[e]]][perms[p][ev[e]]];
      if (!isMax[im]) *invariant = 0;
      seen[im] = 1;
    }
  }
  free(seen);
  free(perms);
  return c;
}

static int fail = 0;
static void check(int ok, const char *msg) {
  printf("%s %s\n", ok ? "ok  " : "FAIL", msg);
  if (!ok) fail = 1;
}

static void run(int nn, int k) {
  n = nn; a = k + 1; M = n * (n - 1) / 2;
  int idx = 0;
  for (int i = 0; i < n; i++)
    for (int j = i + 1; j < n; j++) { eu[idx] = i; ev[idx] = j; idx++; }
  for (int X = 0; X < (1 << n); X++) {
    inX[X] = 0;
    for (int e = 0; e < M; e++)
      if ((X >> eu[e] & 1) && (X >> ev[e] & 1)) inX[X] |= 1u << e;
  }
  uint32_t N = 1u << M;
  unsigned char *D = malloc(N);   /* D[m] = 1 iff taubar(m) <= k */
  long lemma_bad = 0;
  for (uint32_t m = 0; m < N; m++) {
    int ok = 1;
    for (uint32_t r = m; r && ok; r &= r - 1)
      if (!D[m & ~(r & -r)]) ok = 0;
    if (ok && m) {
      int vs = 0;
      for (int e = 0; e < M; e++) if (m >> e & 1) vs |= (1 << eu[e]) | (1 << ev[e]);
      if (decomposes(m, __builtin_popcount(vs))) ok = 0;
    }
    D[m] = ok;
    if (ok != sparse(m)) lemma_bad++;
  }
  long maximal = 0, maximal_wrong_size = 0, b_count = 0, mismatch = 0;
  unsigned char *isMax = calloc(N, 1);
  int target = a * (n - 1) - 1;
  uint32_t full = N - 1;
  for (uint32_t m = 0; m < N; m++) {
    int mx = D[m];
    for (int e = 0; e < M && mx; e++)
      if (!(m >> e & 1) && D[m | 1u << e]) mx = 0;
    int b = D[m] && __builtin_popcount(m) == target;
    isMax[m] = (unsigned char)mx;
    if (mx) { maximal++; if (__builtin_popcount(m) != target) maximal_wrong_size++; }
    if (b) b_count++;
    if (n >= 2 * a && mx != b) mismatch++;
    if (n < 2 * a && mx != (m == full)) mismatch++;
  }
  char msg[256];
  snprintf(msg, sizeof msg, "k=%d n=%d: Lemma 2.1 holds for all %u edge sets", k, n, N);
  check(lemma_bad == 0, msg);
  if (n >= 2 * a) {
    snprintf(msg, sizeof msg,
             "k=%d n=%d: %ld tau_k-maximal graphs, all with %d edges; (a) <=> (b) on every graph",
             k, n, maximal, target);
    check(maximal_wrong_size == 0 && mismatch == 0 && maximal == b_count && maximal > 0, msg);
  } else {
    snprintf(msg, sizeof msg, "k=%d n=%d: K_n is the only tau_k-maximal graph", k, n);
    check(mismatch == 0 && maximal == 1, msg);
  }
  if (n >= 2 * a) {
    int inv;
    long cl = classes(isMax, N, &inv);
    static const long laman[8] = {0, 1, 1, 1, 1, 3, 13, 70};  /* OEIS A227117 */
    snprintf(msg, sizeof msg, "k=%d n=%d: %ld isomorphism class%s%s", k, n, cl, cl == 1 ? "" : "es",
             k == 1 ? " (OEIS A227117: minimally rigid graphs)" : "");
    check(inv && (k != 1 || cl == laman[n]), msg);
  }
  free(isMax);
  free(D);
}

int main(void) {
  for (int k = 1; k <= 3; k++)
    for (int nn = 2; nn <= 7; nn++) run(nn, k);
  puts(fail ? "SOME CHECKS FAILED" : "ALL OK");
  return fail;
}
