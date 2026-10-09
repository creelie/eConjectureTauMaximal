**All τ_k-maximal graphs have the same size**, by Deep Bhattacharjee.

A graph is τ_k-maximal if none of its subgraphs has k+1 edge-disjoint spanning trees, but adding any missing edge creates one. Wang and Tian conjectured that every τ_k-maximal graph on n ≥ 2k+2 vertices has exactly (k+1)(n−1)−1 edges. The paper proves it.

| Step | Content |
|---|---|
| Lemma 2.1 | τ̄(G) ≤ k iff every vertex set X with \|X\| ≥ 2 spans at most (k+1)(\|X\|−1)−1 edges (Nash-Williams–Tutte) |
| Lemmas 3.1–3.2 | Tight sets; a maximal sparse edge set has at least as many edges as any sparse one |
| Lemma 4.1 | An explicit sparse graph with (k+1)(n−1)−1 edges |
| Theorem 1.1 | G is τ_k-maximal iff it is (k+1)-sparse with (k+1)(n−1)−1 edges |

The proofs are by hand. A Lean 4 proof with Mathlib covers Lemmas 3.1, 3.2, 4.1 and Theorem 1.1 in sparse form for every n and k, using only the standard axioms. Exhaustive checks in C and Python decide τ̄ directly on every graph with up to seven vertices; for k = 1 the isomorphism-class counts 1, 3, 13, 70 match the minimally rigid graphs of OEIS A227117. Further checks run in C++, Bash, Julia (the Lee–Streinu pebble game) and a Lean kernel certificate.

Files:
- `tau-maximal-graphs.pdf`: the paper
- `tau-maximal-graphs-tex.zip`: LaTeX source with the figure as PNG (and its TikZ source)
- `tau-maximal-graphs-arxiv.tar.gz`: LaTeX source with the figure as PDF, ready for arXiv

Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.
