# All τ_k-maximal graphs have the same size

Deep Bhattacharjee

For a graph H with at least two vertices let τ(H) be the largest number of edge-disjoint spanning
trees of H, and let τ̄(G) be the largest τ(H) over subgraphs H of G. A graph G is τ_k-maximal if
τ̄(G) ≤ k but τ̄(G + e) ≥ k + 1 for every missing edge e. Wang and Tian (*Extremal graphs with no
subgraph admitting k+1 edge-disjoint spanning trees*, arXiv:2606.28198, Conjecture 1) proved that a
τ_k-maximal graph on n ≥ 2k + 2 vertices has at most (k+1)(n−1)−1 edges, built examples with exactly
that many, settled k = 1, and conjectured that every τ_k-maximal graph on n ≥ 2k + 2 vertices has
exactly (k+1)(n−1)−1 edges.

The conjecture is true. With a = k + 1:

1. By the theorem of Nash-Williams and Tutte, τ̄(G) ≤ k exactly when every vertex set X with
   |X| ≥ 2 spans at most a(|X|−1)−1 edges (G is *a-sparse*). So a τ_k-maximal graph is a maximal
   a-sparse edge set of K_n.
2. An exchange argument with tight sets (vertex sets meeting the bound with equality) shows that a
   maximal sparse set has at least as many edges as any sparse set, so all maximal sparse sets have
   the same size. In matroid language they are the bases of a count matroid.
3. An explicit sparse graph G₀ with a(n−1)−1 edges, K_{2a} minus an edge with every other vertex
   joined to a fixed a of its vertices, shows that the common size is a(n−1)−1.

So G is τ_k-maximal if and only if it is (k+1)-sparse with (k+1)(n−1)−1 edges. For k = 1 these are
exactly the Laman graphs.

## Paper

`preprintTauMaximal/` holds the paper (LaTeX source and the TikZ figure); `dist/` holds the PDF, a
source zip with the figure as PNG and an arXiv tarball, rebuilt by `scripts/build_paper.sh`.

## Checks

```
verification/c/taumax.c             every labelled graph on n <= 7 vertices, k = 1, 2, 3, with tree packings
                                    found directly (no Nash-Williams--Tutte): Lemma 2.1, Theorem 1.1, the
                                    numbers of tau_k-maximal graphs and of their isomorphism classes; for k = 1
                                    the classes number 1, 3, 13, 70 for n = 4..7, as in OEIS A227117
verification/cpp/taumax.cpp         Lemma 2.1 on 8000 random graphs with 8 <= n <= 12 by the partition formula;
                                    greedy growth always ends at a tau_k-maximal graph with (k+1)(n-1)-1 edges;
                                    Lemma 4.1 for a <= 6, n <= 16
verification/shell/check_tau.sh     bash integer arithmetic only: G_0 by subset enumeration for n <= 9, and the
                                    arithmetic of Lemmas 3.1 and 4.1
verification/python/verify_tau.py   every labelled graph on n <= 6 vertices by spanning-tree enumeration
                                    (straight from the definition for n <= 5)
verification/julia/verify_tau.jl    the pebble game of Lee and Streinu: agreement with subset counts, greedy
                                    growth for n <= 40, G_0 for n <= 60, the arithmetic of Lemma 4.1
verification/lean/TauMaximal.lean   Lean 4 kernel check: Theorem 1.1 in sparse form for every edge set of K_4
                                    and K_5 (k = 1), and G_0 for small a and n
verification/lean/mathlib/          Lean 4 + Mathlib proof, for every n and k, of Lemma 3.1, Lemma 3.2,
                                    Lemma 4.1 and Theorem 1.1 in sparse form (a set of edges of K_n is a maximal
                                    (k+1)-sparse set iff it is (k+1)-sparse with (k+1)(n-1)-1 edges); standard
                                    axioms only
```

The Mathlib proof covers every step except Lemma 2.1, which rests on the theorem of Nash-Williams and
Tutte (not in Mathlib); the C and Python programs check Lemma 2.1 on every graph with at most seven and
six vertices by searching for the spanning trees themselves.

`scripts/run_all.sh` runs them all (`MATHLIB=1` also builds the Mathlib proof); the `verify` workflow
runs them on every pull request.

## Citation

See `CITATION.cff`. The Zenodo DOI will be added after the first release.

## Licence

MIT, see `LICENSE`.
