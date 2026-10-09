// taumax.cpp -- randomized and structural checks for "All tau_k-maximal graphs have the same size",
// independent of the C program.
//
// Here taubar(G) >= a is decided with the partition formula of Nash-Williams and Tutte: G[X] has a
// edge-disjoint spanning trees iff  max over partitions P of X of  sum_i (e(P_i) + a)  equals
// e(X) + a. The maximum over partitions is a dynamic program over subsets, O(3^n).
//
//  1. Lemma 2.1 on random graphs with 8 <= n <= 12 and a = k+1 = 2..5;
//  2. greedy growth (random edge order, keep an edge iff the graph stays a-sparse) always stops at
//     a(n-1)-1 edges, and the result is tau_k-maximal by the partition formula;
//  3. Lemma 4.1: G_0 is a-sparse with a(n-1)-1 edges for 2 <= a <= 6, 2a <= n <= 16.
// Prints "ALL OK" when every check passes.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <random>
#include <vector>

static bool failed = false;
static void check(bool ok, const char *msg) {
  std::printf("%s %s\n", ok ? "ok  " : "FAIL", msg);
  if (!ok) failed = true;
}

struct Graph {
  int n;
  std::vector<uint32_t> adj;
  explicit Graph(int n_) : n(n_), adj(n_, 0) {}
  bool has(int u, int v) const { return adj[u] >> v & 1; }
  void add(int u, int v) { adj[u] |= 1u << v; adj[v] |= 1u << u; }
  void del(int u, int v) { adj[u] &= ~(1u << v); adj[v] &= ~(1u << u); }
  // e(X) for every X
  std::vector<int> induced() const {
    std::vector<int> e(1u << n, 0);
    for (uint32_t X = 1; X < (1u << n); X++) {
      int v = __builtin_ctz(X);
      uint32_t Y = X & (X - 1);
      e[X] = e[Y] + __builtin_popcount(adj[v] & Y);
    }
    return e;
  }
};

static bool sparse(const Graph &G, int a) {
  std::vector<int> e = G.induced();
  for (uint32_t X = 0; X < (1u << G.n); X++) {
    int s = __builtin_popcount(X);
    if (s >= 2 && e[X] > a * (s - 1) - 1) return false;
  }
  return true;
}

// taubar(G) >= a, by the Nash-Williams--Tutte partition formula
static bool taubarAtLeast(const Graph &G, int a) {
  int n = G.n;
  std::vector<int> e = G.induced();
  std::vector<int> F(1u << n, 0);
  for (uint32_t X = 1; X < (1u << n); X++) {
    uint32_t low = X & (0u - X), rest = X ^ low;
    int best = -1;
    // parts P containing the lowest vertex of X
    for (uint32_t S = rest;; S = (S - 1) & rest) {
      uint32_t P = S | low;
      int val = e[P] + a + F[X ^ P];
      if (val > best) best = val;
      if (S == 0) break;
    }
    F[X] = best;
    if (__builtin_popcount(X) >= 2 && best == e[X] + a) return true;
  }
  return false;
}

int main() {
  std::mt19937_64 rng(20261009);
  char msg[256];

  // 1. Lemma 2.1 on random graphs of various densities
  for (int a = 2; a <= 5; a++) {
    long tested = 0, bad = 0, sparseCount = 0;
    for (int n = 8; n <= 12; n++)
      for (int t = 0; t < 400; t++) {
        Graph G(n);
        double p = 0.15 + 0.7 * (t % 20) / 19.0;
        std::uniform_real_distribution<double> U(0, 1);
        for (int u = 0; u < n; u++)
          for (int v = u + 1; v < n; v++)
            if (U(rng) < p) G.add(u, v);
        bool s = sparse(G, a);
        sparseCount += s;
        if (s == taubarAtLeast(G, a)) bad++;
        tested++;
      }
    std::snprintf(msg, sizeof msg,
                  "a=%d: Lemma 2.1 on %ld random graphs with 8 <= n <= 12 (%ld of them sparse)", a,
                  tested, sparseCount);
    check(bad == 0 && sparseCount > 0 && sparseCount < tested, msg);
  }

  // 2. greedy growth
  for (int a = 2; a <= 5; a++) {
    long runs = 0, bad = 0;
    for (int n = 2 * a; n <= 12; n++)
      for (int t = 0; t < 8; t++) {
        std::vector<std::pair<int, int>> pairs;
        for (int u = 0; u < n; u++)
          for (int v = u + 1; v < n; v++) pairs.push_back({u, v});
        std::shuffle(pairs.begin(), pairs.end(), rng);
        Graph G(n);
        int m = 0;
        for (auto [u, v] : pairs) {
          G.add(u, v);
          if (sparse(G, a)) m++;
          else G.del(u, v);
        }
        bool ok = m == a * (n - 1) - 1 && !taubarAtLeast(G, a);
        for (auto [u, v] : pairs)
          if (ok && !G.has(u, v)) {
            G.add(u, v);
            ok = taubarAtLeast(G, a);
            G.del(u, v);
          }
        runs++;
        if (!ok) bad++;
      }
    std::snprintf(msg, sizeof msg,
                  "a=%d: %ld greedy runs with 2a <= n <= 12 stop at a(n-1)-1 edges at a "
                  "tau_k-maximal graph", a, runs);
    check(bad == 0, msg);
  }

  // 3. G_0
  {
    long graphs = 0, bad = 0;
    for (int a = 2; a <= 6; a++)
      for (int n = 2 * a; n <= 16; n++) {
        Graph G(n);
        for (int u = 0; u < n; u++)
          for (int v = u + 1; v < n; v++) {
            bool inA = u < a;                                   // an end in A = {0..a-1}
            bool inW = u >= a && v < 2 * a && !(u == 2 * a - 2 && v == 2 * a - 1);
            if (inA || inW) G.add(u, v);
          }
        int m = 0;
        for (int u = 0; u < n; u++) m += __builtin_popcount(G.adj[u]);
        m /= 2;
        graphs++;
        if (m != a * (n - 1) - 1 || !sparse(G, a)) bad++;
      }
    std::snprintf(msg, sizeof msg,
                  "Lemma 4.1: G_0 is a-sparse with a(n-1)-1 edges for all %ld pairs 2 <= a <= 6, "
                  "2a <= n <= 16", graphs);
    check(bad == 0, msg);
  }

  std::puts(failed ? "SOME CHECKS FAILED" : "ALL OK");
  return failed ? 1 : 0;
}
