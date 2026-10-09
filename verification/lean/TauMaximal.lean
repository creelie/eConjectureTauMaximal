/-
  Kernel-checked finite certificate for "All τ_k-maximal graphs have the same size".

  Edge sets of K_n are bit masks over the pairs (i, j), i < j < n, in lexicographic order, and
  `a = k + 1`. A mask is `a`-sparse when every vertex set X with |X| ≥ 2 spans at most
  a(|X| - 1) - 1 of its edges.

  * `exhaustive`: for (n, a) = (4, 2), (5, 2) and every edge set m of K_n, m is a maximal
    `a`-sparse set if and only if m is `a`-sparse with a(n-1)-1 edges (Theorem 1.1 after Lemma 2.1),
    and the numbers of such sets are 6 and 100.
  * `example_small`: the graph G₀ of Lemma 4.1 is `a`-sparse with a(n-1)-1 edges for
    a = 2, 3, 4 and 2a ≤ n ≤ 2a + 2.

  The statement for all n and a, with the exchange argument of Lemma 3.2 and Lemma 4.1 in general,
  is proved with Mathlib in `mathlib/TauMaximalMathlib.lean`. This file uses Lean 4 core only;
  every statement is checked by the kernel (`decide +kernel`).
-/

/-- the pairs (i, j), i < j < n -/
def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => ((List.range n).filter (i < ·)).map fun j => (i, j)

/-- number of set bits among the lowest `w` bits -/
def popc : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, m => m % 2 + popc w (m / 2)

/-- the edges of K_n inside the vertex set X, as a mask -/
def inX (n X : Nat) : Nat :=
  ((pairs n).zipIdx.filter fun ((i, j), _) => X.testBit i && X.testBit j).foldl
    (fun acc (_, e) => acc ||| (1 <<< e)) 0

def sparseB (n a m : Nat) : Bool :=
  let M := (pairs n).length
  (List.range (2 ^ n)).all fun X =>
    let s := popc n X
    s < 2 || popc M (m &&& inX n X) + a + 1 ≤ a * s

def maximalB (n a m : Nat) : Bool :=
  sparseB n a m && (List.range (pairs n).length).all fun e =>
    m.testBit e || !sparseB n a (m ||| (1 <<< e))

def bB (n a m : Nat) : Bool :=
  sparseB n a m && popc (pairs n).length m + a + 1 == a * n

/-- the masks m of K_n with `maximalB` -/
def maxCount (n a : Nat) : Nat :=
  ((List.range (2 ^ (pairs n).length)).filter fun m => maximalB n a m).length

def agree (n a : Nat) : Bool :=
  (List.range (2 ^ (pairs n).length)).all fun m => maximalB n a m == bB n a m

theorem exhaustive :
    agree 4 2 = true ∧ maxCount 4 2 = 6 ∧
    agree 5 2 = true ∧ maxCount 5 2 = 100 := by
  decide +kernel

/-- G₀ on {0, …, n-1}: the pairs with an end in A = {0, …, a-1}, and the pairs inside
    W = {a, …, 2a-1} other than (2a-2, 2a-1) -/
def G0 (n a : Nat) : Nat :=
  ((pairs n).zipIdx.filter fun ((i, j), _) =>
      i < a || (j < 2 * a && !(i == 2 * a - 2 && j == 2 * a - 1))).foldl
    (fun acc (_, e) => acc ||| (1 <<< e)) 0

def exampleOK (n a : Nat) : Bool :=
  bB n a (G0 n a)

theorem example_small :
    [(4, 2), (5, 2), (6, 2), (6, 3), (7, 3), (8, 3), (8, 4), (9, 4), (10, 4)].all
      (fun (n, a) => exampleOK n a) = true := by
  decide +kernel

#print axioms exhaustive
#print axioms example_small
