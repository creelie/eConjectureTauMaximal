"""verify_tau.py -- exhaustive check of "All tau_k-maximal graphs have the same size" for small n,
straight from the definitions, with a third algorithm (spanning-tree enumeration).

* n <= 5: for every labelled graph G and every vertex set X with |X| >= 2, list the spanning trees
  of G[X] and look for a pairwise edge-disjoint ones; this gives taubar(G) >= a by definition.
* n = 6: every proper subgraph test is inherited (taubar(G) >= a iff some G - e has it, or the
  edges of G are exactly a edge-disjoint spanning trees of the vertices they touch), and the last
  condition is tested by the same tree enumeration.

For a = k + 1 in {2, 3} this checks Lemma 2.1 (taubar <= k iff a-sparse), that every
tau_k-maximal graph has (k+1)(n-1)-1 edges when n >= 2k+2, the equivalence (a) <=> (b) of
Theorem 1.1, and the counts 6, 100, 3355 (k = 1, n = 4, 5, 6) and 15 (k = 2, n = 6) found by the
C program. Prints "ALL OK" when every check passes.
"""
from itertools import combinations
import sys

failed = False


def check(ok, msg):
    global failed
    print(("ok   " if ok else "FAIL ") + msg)
    failed |= not ok


def acyclic(edges, verts):
    parent = {v: v for v in verts}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for u, v in edges:
        ru, rv = find(u), find(v)
        if ru == rv:
            return False
        parent[ru] = rv
    return True


def spanning_trees(edges, verts):
    """all spanning trees of (verts, edges), as frozensets of edges"""
    return [frozenset(T) for T in combinations(edges, len(verts) - 1) if acyclic(T, verts)]


def packs(trees, a, used=frozenset(), start=0):
    """are there a pairwise disjoint trees (indices >= start) avoiding `used`?"""
    if a == 0:
        return True
    for i in range(start, len(trees)):
        if not (trees[i] & used) and packs(trees, a - 1, used | trees[i], i + 1):
            return True
    return False


def all_pairs(n):
    return list(combinations(range(n), 2))


def taubar_direct(n, E, a):
    """taubar(G) >= a, straight from the definition"""
    for size in range(2, n + 1):
        for X in combinations(range(n), size):
            Xs = set(X)
            EX = [e for e in E if e[0] in Xs and e[1] in Xs]
            if len(EX) < a * (size - 1):
                continue
            if packs(spanning_trees(EX, X), a):
                return True
    return False


def is_union_of_trees(E, a):
    verts = sorted({v for e in E for v in e})
    if len(E) != a * (len(verts) - 1):
        return False
    return packs(spanning_trees(list(E), verts), a)


def sparse(n, E, a):
    for size in range(2, n + 1):
        for X in combinations(range(n), size):
            Xs = set(X)
            if sum(1 for e in E if e[0] in Xs and e[1] in Xs) > a * (size - 1) - 1:
                return False
    return True


def run(n, k, direct):
    a = k + 1
    P = all_pairs(n)
    N = 1 << len(P)
    edges = [[P[i] for i in range(len(P)) if m >> i & 1] for m in range(N)]
    low = [True] * N  # taubar <= k
    for m in range(N):
        if direct:
            low[m] = not taubar_direct(n, edges[m], a)
        else:
            ok = all(low[m & ~(1 << i)] for i in range(len(P)) if m >> i & 1)
            low[m] = ok and not (m and is_union_of_trees(edges[m], a))
    lemma = all(low[m] == sparse(n, edges[m], a) for m in range(N))
    check(lemma, f"k={k} n={n}: Lemma 2.1 on all {N} labelled graphs")
    target = a * (n - 1) - 1
    maximal = [m for m in range(N)
               if low[m] and all(not low[m | 1 << i] for i in range(len(P)) if not m >> i & 1)]
    condb = [m for m in range(N) if low[m] and len(edges[m]) == target]
    ok = maximal == condb and all(len(edges[m]) == target for m in maximal)
    check(ok, f"k={k} n={n}: {len(maximal)} tau_k-maximal graphs, all with {target} edges, "
              f"and (a) <=> (b)")
    return len(maximal)


counts = {(1, 4): 6, (1, 5): 100, (1, 6): 3355, (2, 6): 15}
for (k, n), want in counts.items():
    got = run(n, k, direct=(n <= 5))
    check(got == want, f"k={k} n={n}: the count {got} agrees with the C program")

print("SOME CHECKS FAILED" if failed else "ALL OK")
sys.exit(1 if failed else 0)
