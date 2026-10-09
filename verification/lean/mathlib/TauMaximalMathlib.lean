import Mathlib

/-!
# Maximal sparse graphs have the same size

Lean 4 / Mathlib proof of the counting part of

  D. Bhattacharjee, *All τ_k-maximal graphs have the same size*.

Write `a = k + 1 ≥ 2`. A set `E` of edges of the complete graph on a finite vertex type `V` is
`a`-sparse if `e_E(X) ≤ a (|X| - 1) - 1` for every vertex set `X` with `|X| ≥ 2`, where `e_E(X)`
counts the edges of `E` with both ends in `X`. Lemma 2.1 of the paper (the theorem of
Nash-Williams and Tutte, which is not in Mathlib) says that a graph is `τ_k`-maximal exactly when
its edge set is a maximal `(k+1)`-sparse set. This file proves everything after that step:

* `supermod`, `tight_union`, `exists_tight` (Lemma 3.1);
* `card_le_of_maximal` (Lemma 3.2): on any finite vertex set, a maximal sparse set has at least as
  many edges as any sparse set;
* `example_sparse`, `card_G0` (Lemma 4.1): for `n ≥ 2a` the graph `G₀` is sparse with
  `a(n-1)-1` edges;
* `maximal_iff` (Theorem 1.1, (a) ⟺ (b), in sparse form): for `a ≥ 2` and `n ≥ 2a`, a set of
  edges of `K_n` is a maximal `a`-sparse set if and only if it is `a`-sparse with `a(n-1)-1` edges;
* `conjecture`: every maximal `(k+1)`-sparse set of edges of `K_n`, `n ≥ 2k+2`, has exactly
  `(k+1)(n-1)-1` edges.
-/

open Finset

namespace TauMaximal

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `E` with both ends in `X`. -/
def eIn (E : Finset (Sym2 V)) (X : Finset V) : Finset (Sym2 V) := E.filter (· ∈ X.sym2)

/-- `E` is `a`-sparse: `e_E(X) + a + 1 ≤ a |X|` whenever `|X| ≥ 2`. -/
def Sparse (a : ℕ) (E : Finset (Sym2 V)) : Prop :=
  ∀ X : Finset V, 2 ≤ #X → #(eIn E X) + a + 1 ≤ a * #X

/-- The edge set of the complete graph on `V`. -/
def K : Finset (Sym2 V) := univ.filter fun e => ¬ e.IsDiag

/-- `X` is tight for `E`: equality in the sparsity condition. -/
def Tight (a : ℕ) (E : Finset (Sym2 V)) (X : Finset V) : Prop :=
  2 ≤ #X ∧ #(eIn E X) + a + 1 = a * #X

instance (a : ℕ) (E : Finset (Sym2 V)) (X : Finset V) : Decidable (Tight a E X) := by
  unfold Tight; infer_instance

/-- A maximal sparse subset of `K`. -/
def MaxSparse (a : ℕ) (E : Finset (Sym2 V)) : Prop :=
  E ⊆ K ∧ Sparse a E ∧ ∀ e ∈ K, e ∉ E → ¬ Sparse a (insert e E)

omit [Fintype V] in
lemma two_le_card {X : Finset V} {e : Sym2 V} (he : e ∈ X.sym2) (hd : ¬ e.IsDiag) :
    2 ≤ #X := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [Finset.mk_mem_sym2_iff] at he
    have huv : u ≠ v := by simpa using hd
    calc 2 = #({u, v} : Finset V) := (card_pair huv).symm
      _ ≤ #X := card_le_card (by intro x; simp only [mem_insert, mem_singleton]
                                 rintro (rfl | rfl) <;> simp [he])

omit [Fintype V] in
lemma mem_sym2_inter {X Y : Finset V} {e : Sym2 V} (hX : e ∈ X.sym2) (hY : e ∈ Y.sym2) :
    e ∈ (X ∩ Y).sym2 := by
  rw [mem_sym2_iff] at *
  intro v hv
  exact mem_inter.2 ⟨hX v hv, hY v hv⟩

omit [Fintype V] in
lemma eIn_mono {E : Finset (Sym2 V)} {X Y : Finset V} (h : X ⊆ Y) : eIn E X ⊆ eIn E Y := by
  intro e he
  simp only [eIn, mem_filter] at *
  exact ⟨he.1, Finset.sym2_mono h he.2⟩

/-- `e_E` is supermodular. -/
lemma supermod (E : Finset (Sym2 V)) (X Y : Finset V) :
    #(eIn E X) + #(eIn E Y) ≤ #(eIn E (X ∪ Y)) + #(eIn E (X ∩ Y)) := by
  have hi : eIn E X ∩ eIn E Y = eIn E (X ∩ Y) := by
    ext e
    simp only [eIn, mem_inter, mem_filter, mem_sym2_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, -, h3⟩; exact ⟨h1, fun v hv => ⟨h2 v hv, h3 v hv⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun v hv => (h2 v hv).1⟩, h1, fun v hv => (h2 v hv).2⟩
  have hu : eIn E X ∪ eIn E Y ⊆ eIn E (X ∪ Y) :=
    union_subset (eIn_mono subset_union_left) (eIn_mono subset_union_right)
  rw [← card_union_add_card_inter, hi]
  exact Nat.add_le_add_right (card_le_card hu) _

/-- Two tight sets sharing at least two vertices have a tight union. -/
lemma tight_union {a : ℕ} {E : Finset (Sym2 V)} (hE : Sparse a E) {X Y : Finset V}
    (hX : Tight a E X) (hY : Tight a E Y) (hXY : 2 ≤ #(X ∩ Y)) : Tight a E (X ∪ Y) := by
  have h2 : 2 ≤ #(X ∪ Y) := hX.1.trans (card_le_card subset_union_left)
  refine ⟨h2, le_antisymm (hE _ h2) ?_⟩
  have hs := supermod E X Y
  have hi := hE _ hXY
  have hc : #(X ∪ Y) + #(X ∩ Y) = #X + #Y := card_union_add_card_inter X Y
  have hc' : a * #(X ∪ Y) + a * #(X ∩ Y) = a * #X + a * #Y := by
    rw [← mul_add, hc, mul_add]
  have := hX.2
  have := hY.2
  omega

/-- If adding the edge `e` destroys sparsity, some tight set contains both ends of `e`. -/
lemma exists_tight {a : ℕ} {E : Finset (Sym2 V)} (hE : Sparse a E) {e : Sym2 V} (he : e ∉ E)
    (hne : ¬ Sparse a (insert e E)) : ∃ X, Tight a E X ∧ e ∈ X.sym2 := by
  simp only [Sparse, not_forall, not_le] at hne
  obtain ⟨X, hX, hlt⟩ := hne
  have hb := hE X hX
  by_cases heX : e ∈ X.sym2
  · refine ⟨X, ⟨hX, ?_⟩, heX⟩
    have : eIn (insert e E) X = insert e (eIn E X) := by
      unfold eIn; simp only [filter_insert, heX, ↓reduceIte]
    rw [this, card_insert_of_notMem (by simp [eIn, he])] at hlt
    omega
  · have : eIn (insert e E) X = eIn E X := by
      unfold eIn; simp only [filter_insert, heX, ↓reduceIte]
    rw [this] at hlt
    omega

/-- The union of all tight sets containing both ends of `e`. -/
def closure (a : ℕ) (E : Finset (Sym2 V)) (e : Sym2 V) : Finset V :=
  ((univ : Finset (Finset V)).filter fun X => Tight a E X ∧ e ∈ X.sym2).sup id

lemma sup_tight {a : ℕ} {E : Finset (Sym2 V)} (hE : Sparse a E) {e : Sym2 V} (hd : ¬ e.IsDiag)
    (S : Finset (Finset V)) (hS : S.Nonempty) (hT : ∀ X ∈ S, Tight a E X ∧ e ∈ X.sym2) :
    Tight a E (S.sup id) ∧ e ∈ (S.sup id).sym2 := by
  induction S using Finset.induction_on with
  | empty => exact absurd hS (by simp)
  | insert X S hXS ih =>
    rw [sup_insert, id]
    have hX := hT X (mem_insert_self X S)
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simpa using hX
    · obtain ⟨hT', he'⟩ := ih hne (fun Y hY => hT Y (mem_insert_of_mem hY))
      exact ⟨tight_union hE hX.1 hT' (two_le_card (mem_sym2_inter hX.2 he') hd),
        Finset.sym2_mono subset_union_left hX.2⟩

lemma closure_spec {a : ℕ} {E : Finset (Sym2 V)} (hE : Sparse a E) {e : Sym2 V}
    (hd : ¬ e.IsDiag) (h : ∃ X, Tight a E X ∧ e ∈ X.sym2) :
    Tight a E (closure a E e) ∧ e ∈ (closure a E e).sym2 := by
  obtain ⟨X, hX⟩ := h
  exact sup_tight hE hd _ ⟨X, mem_filter.2 ⟨mem_univ _, hX⟩⟩ (fun Y hY => (mem_filter.1 hY).2)

lemma le_closure {a : ℕ} {E : Finset (Sym2 V)} {e : Sym2 V} {X : Finset V}
    (hX : Tight a E X) (he : e ∈ X.sym2) : X ⊆ closure a E e :=
  le_sup (f := id) (mem_filter.2 ⟨mem_univ _, hX, he⟩)

/-- The maximal tight sets. -/
def maxTight (a : ℕ) (E : Finset (Sym2 V)) : Finset (Finset V) :=
  (univ : Finset (Finset V)).filter fun X => Tight a E X ∧ ∀ Y, Tight a E Y → X ⊆ Y → Y = X

lemma covered {a : ℕ} {E : Finset (Sym2 V)} (hE : Sparse a E) {e : Sym2 V} (hd : ¬ e.IsDiag)
    (h : ∃ X, Tight a E X ∧ e ∈ X.sym2) : ∃ M ∈ maxTight a E, e ∈ M.sym2 := by
  obtain ⟨hT, he⟩ := closure_spec hE hd h
  refine ⟨closure a E e, ?_, he⟩
  simp only [maxTight, mem_filter, mem_univ, true_and]
  refine ⟨hT, fun Y hY hsub => le_antisymm (le_closure hY (Finset.sym2_mono hsub he)) hsub⟩

/-- Distinct maximal tight sets share no edge of `K`. -/
lemma disjoint_maxTight {a : ℕ} {E : Finset (Sym2 V)} (hE : Sparse a E) (J : Finset (Sym2 V))
    (hJ : J ⊆ K) : (maxTight a E : Set (Finset V)).PairwiseDisjoint (eIn J) := by
  intro X hX Y hY hne
  simp only [coe_filter, maxTight, mem_univ, true_and] at hX hY
  rw [Function.onFun, Finset.disjoint_left]
  intro e heX heY
  simp only [eIn, mem_filter] at heX heY
  have hd : ¬ e.IsDiag := by have := hJ heX.1; simpa [K] using this
  have hU := tight_union hE hX.1 hY.1 (two_le_card (mem_sym2_inter heX.2 heY.2) hd)
  exact hne ((hX.2 _ hU subset_union_left).symm.trans (hY.2 _ hU subset_union_right))

/-- Counting the edges of `J` through the maximal tight sets of `E`. -/
lemma card_split {a : ℕ} {E : Finset (Sym2 V)} (hE : Sparse a E) (J : Finset (Sym2 V))
    (hJ : J ⊆ K) :
    #J = ∑ X ∈ maxTight a E, #(eIn J X) +
      #(J.filter fun e => ∀ X ∈ maxTight a E, e ∉ X.sym2) := by
  rw [← card_biUnion (disjoint_maxTight hE J hJ)]
  have : (maxTight a E).biUnion (eIn J) = J.filter fun e => ¬ ∀ X ∈ maxTight a E, e ∉ X.sym2 := by
    ext e
    simp only [mem_biUnion, eIn, mem_filter, not_forall, not_not, exists_prop]
    constructor
    · rintro ⟨X, hX, heJ, he⟩; exact ⟨heJ, X, hX, he⟩
    · rintro ⟨heJ, X, hX, he⟩; exact ⟨X, hX, heJ, he⟩
  rw [this]
  have := card_filter_add_card_filter_not (s := J) (fun e => ∀ X ∈ maxTight a E, e ∉ X.sym2)
  omega

/-- **Lemma 3.2.** A maximal sparse set has at least as many edges as any sparse set. -/
theorem card_le_of_maximal {a : ℕ} {I J : Finset (Sym2 V)} (hI : MaxSparse a I)
    (hJ : J ⊆ K) (hJs : Sparse a J) : #J ≤ #I := by
  obtain ⟨hIK, hIs, hmax⟩ := hI
  rw [card_split hIs J hJ, card_split hIs I hIK]
  apply add_le_add
  · apply sum_le_sum
    intro X hX
    simp only [maxTight, mem_filter, mem_univ, true_and] at hX
    have h1 := hX.1.2
    have h2 := hJs X hX.1.1
    omega
  · apply card_le_card
    intro e he
    simp only [mem_filter] at he ⊢
    refine ⟨?_, he.2⟩
    by_contra heI
    have hd : ¬ e.IsDiag := by have := hJ he.1; simpa [K] using this
    obtain ⟨M, hM, heM⟩ := covered hIs hd (exists_tight hIs heI (hmax e (hJ he.1) heI))
    exact he.2 M hM heM

lemma eIn_univ (E : Finset (Sym2 V)) : eIn E univ = E := by
  simp [eIn]

/-- Taking `X = V`: a sparse set has at most `a(n-1)-1` edges. -/
lemma card_le_of_sparse {a : ℕ} {E : Finset (Sym2 V)} (hE : Sparse a E) (hV : 2 ≤ Fintype.card V) :
    #E + a + 1 ≤ a * Fintype.card V := by
  simpa [eIn_univ] using hE univ (by simpa using hV)

lemma filter_mem_sym2 (S : Finset V) :
    (K : Finset (Sym2 V)).filter (· ∈ S.sym2) = S.offDiag.image Sym2.mk.uncurry := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [K, mem_filter, mem_univ, true_and, Finset.mk_mem_sym2_iff, mem_image, mem_offDiag,
      Prod.exists, Sym2.mk_isDiag_iff, Function.uncurry_apply_pair]
    constructor
    · rintro ⟨huv, hu, hv⟩; exact ⟨u, v, ⟨hu, hv, huv⟩, rfl⟩
    · rintro ⟨x, y, ⟨hx, hy, hxy⟩, h⟩
      rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hxy, hx, hy⟩
      · exact ⟨Ne.symm hxy, hy, hx⟩

/-- `K` has `C(|S|, 2)` edges inside a vertex set `S`. -/
lemma card_filter_mem_sym2 (S : Finset V) :
    #((K : Finset (Sym2 V)).filter (· ∈ S.sym2)) = (#S).choose 2 := by
  rw [filter_mem_sym2, Sym2.card_image_offDiag]

lemma card_eIn_le (E : Finset (Sym2 V)) (hE : E ⊆ K) (X : Finset V) :
    #(eIn E X) ≤ (#X).choose 2 := by
  rw [← card_filter_mem_sym2]
  exact card_le_card fun e he => by
    simp only [eIn, mem_filter] at he ⊢; exact ⟨hE he.1, he.2⟩

end General

lemma two_mul_choose_two (x : ℕ) : 2 * x.choose 2 = x * (x - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self x).two_dvd]

/-! ### The example `G₀` (Lemma 4.1)

The vertices are `0, …, n-1`; `A = {0, …, a-1}`, `C = {0, …, 2a-1}`, `W = C \ A`, and
`D = {2a-2, 2a-1}` is the pair `w w'`. The edges of `G₀` are those with an end in `A` together
with those inside `W` other than `w w'`; so `G₀[C]` is `K_{2a}` minus one edge and every vertex
outside `C` is joined to exactly the vertices of `A`. -/

section Example

variable (a n : ℕ)

/-- `A = {0, …, a-1}` -/
def A : Finset (Fin n) := univ.filter fun v => (v : ℕ) < a
/-- `C = {0, …, 2a-1}` -/
def C : Finset (Fin n) := univ.filter fun v => (v : ℕ) < 2 * a
/-- `W = {a, …, 2a-1}` -/
def W : Finset (Fin n) := C a n \ A a n
/-- `D = {2a-2, 2a-1}`, the missing edge `w w'` -/
def D : Finset (Fin n) := univ.filter fun v => 2 * a - 2 ≤ (v : ℕ) ∧ (v : ℕ) < 2 * a

/-- The graph `G₀` of Lemma 4.1. -/
def G0 : Finset (Sym2 (Fin n)) :=
  K.filter fun e => e ∉ (A a n)ᶜ.sym2 ∨ (e ∈ (W a n).sym2 ∧ e ∉ (D a n).sym2)

variable {a n}

lemma card_A (hn : a ≤ n) : #(A a n) = a := by
  rw [A, Fin.card_filter_val_lt]; omega

lemma card_C (hn : 2 * a ≤ n) : #(C a n) = 2 * a := by
  rw [C, Fin.card_filter_val_lt]; omega

lemma A_sub_C : A a n ⊆ C a n := by
  intro v; simp only [A, C, mem_filter, mem_univ, true_and]; omega

lemma card_W (hn : 2 * a ≤ n) : #(W a n) = a := by
  rw [W, card_sdiff_of_subset A_sub_C, card_C hn, card_A (by omega)]; omega

lemma D_sub_W (ha : 2 ≤ a) : D a n ⊆ W a n := by
  intro v; simp only [D, W, A, C, mem_sdiff, mem_filter, mem_univ, true_and]; omega

lemma card_D (ha : 2 ≤ a) (hn : 2 * a ≤ n) : #(D a n) = 2 := by
  have : D a n = {⟨2 * a - 2, by omega⟩, ⟨2 * a - 1, by omega⟩} := by
    ext v; simp only [D, mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
    omega
  rw [this, card_pair]; simp [Fin.ext_iff]; omega

/-- `C(n,2) + C(a,2) = C(n-a,2) + a(n-1)` -/
lemma choose_identity (m : ℕ) : (m + a).choose 2 + a.choose 2 = m.choose 2 + a * (m + a - 1) := by
  have h1 := two_mul_choose_two (m + a)
  have h2 := two_mul_choose_two a
  have h3 := two_mul_choose_two m
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_add, Nat.choose]
    have : a * (a - 1) = 2 * a.choose 2 := h2.symm
    simp at *; omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2 h3 ⊢
  have : m' + 1 + (a' + 1) - 1 = m' + a' + 1 := by omega
  rw [this] at h1 ⊢
  nlinarith

lemma card_G0 (ha : 2 ≤ a) (hn : 2 * a ≤ n) : #(G0 a n) + a + 1 = a * n := by
  -- edges with an end in `A`, and edges inside `W` but not inside `D`
  have hsplit : G0 a n = (K.filter fun e => e ∉ (A a n)ᶜ.sym2) ∪
      ((K.filter (· ∈ (W a n).sym2)) \ (K.filter (· ∈ (D a n).sym2))) := by
    ext e; simp only [G0, mem_union, mem_filter, mem_sdiff]; tauto
  have hdisj : Disjoint (K.filter fun e => e ∉ (A a n)ᶜ.sym2)
      ((K.filter (· ∈ (W a n).sym2)) \ (K.filter (· ∈ (D a n).sym2))) := by
    rw [disjoint_left]
    intro e h1 h2
    simp only [mem_filter, mem_sdiff] at h1 h2
    apply h1.2
    refine Finset.sym2_mono (fun v hv => ?_) h2.1.2
    simp only [W, mem_sdiff] at hv; exact mem_compl.2 hv.2
  have hAc : (K.filter fun e => e ∉ (A a n)ᶜ.sym2) =
      K \ (K.filter (· ∈ (A a n)ᶜ.sym2)) := by
    ext e; simp only [mem_filter, mem_sdiff]; tauto
  have hD : K.filter (· ∈ (D a n).sym2) ⊆ K.filter (· ∈ (W a n).sym2) := by
    intro e he; simp only [mem_filter] at he ⊢
    exact ⟨he.1, Finset.sym2_mono (D_sub_W ha) he.2⟩
  rw [hsplit, card_union_of_disjoint hdisj, hAc, card_sdiff_of_subset (filter_subset _ _),
    card_sdiff_of_subset hD, card_filter_mem_sym2, card_filter_mem_sym2, card_filter_mem_sym2,
    card_compl, card_W hn, card_D ha hn, card_A (by omega), Fintype.card_fin]
  have hK : #(K : Finset (Sym2 (Fin n))) = n.choose 2 := by
    have := card_filter_mem_sym2 (univ : Finset (Fin n))
    rw [card_univ, Fintype.card_fin] at this
    rw [← this]; congr 1; ext e; simp
  rw [hK, Nat.choose_self]
  have hid := choose_identity (a := a) (n - a)
  rw [Nat.sub_add_cancel (by omega : a ≤ n)] at hid
  have hle : (n - a).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 (Nat.sub_le n a)
  have h2 : 2 ≤ a.choose 2 + 1 := by
    have := two_mul_choose_two a
    have : 2 * 1 ≤ a * (a - 1) := Nat.mul_le_mul ha (by omega)
    omega
  have : a * n = a * (n - 1) + a := by
    rw [← Nat.mul_succ]; congr 1; omega
  omega

lemma G0_sub_K : G0 a n ⊆ K := filter_subset _ _

/-- `C(x,2) + a + 1 ≤ a x` for `2 ≤ x ≤ 2a - 1` -/
lemma core_ineq {x : ℕ} (hx : 2 ≤ x) (hxa : x + 1 ≤ 2 * a) : x.choose 2 + a + 1 ≤ a * x := by
  have h := two_mul_choose_two x
  obtain ⟨p, rfl⟩ : ∃ p, x = p + 2 := ⟨x - 2, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, 2 * a = p + 3 + q := ⟨2 * a - (p + 3), by omega⟩
  have hpq : 1 ≤ p + q := by omega
  have : p + 2 - 1 = p + 1 := by omega
  rw [this] at h
  have hq' : 2 * a * (p + 2) = (p + 3 + q) * (p + 2) := by rw [hq]
  nlinarith

/-- The core: inside `C`, `G₀` is `K_{2a}` minus the edge `w w'`. -/
lemma core_sparse (ha : 2 ≤ a) (hn : 2 * a ≤ n) {X : Finset (Fin n)} (hXC : X ⊆ C a n)
    (hX : 2 ≤ #X) : #(eIn (G0 a n) X) + a + 1 ≤ a * #X := by
  have hle : #X ≤ 2 * a := (card_le_card hXC).trans (card_C hn).le
  rcases Nat.lt_or_ge #X (2 * a) with hlt | hge
  · exact (Nat.add_le_add_right (Nat.add_le_add_right (card_eIn_le _ G0_sub_K X) _) _).trans
      (core_ineq hX (by omega))
  · have hXeq : X = C a n := eq_of_subset_of_card_le hXC (by rw [card_C hn]; omega)
    subst hXeq
    have hsub : eIn (G0 a n) (C a n) ⊆
        (K.filter (· ∈ (C a n).sym2)) \ (K.filter (· ∈ (D a n).sym2)) := by
      intro e he
      simp only [eIn, G0, mem_filter, mem_sdiff] at he ⊢
      refine ⟨⟨he.1.1, he.2⟩, fun hD => ?_⟩
      rcases he.1.2 with h | h
      · apply h
        refine Finset.sym2_mono (fun v hv => ?_) hD.2
        have := D_sub_W ha hv
        simp only [W, mem_sdiff] at this; exact mem_compl.2 this.2
      · exact h.2 hD.2
    have hDC : K.filter (· ∈ (D a n).sym2) ⊆ K.filter (· ∈ (C a n).sym2) := by
      intro e he; simp only [mem_filter] at he ⊢
      exact ⟨he.1, Finset.sym2_mono ((D_sub_W ha).trans sdiff_subset) he.2⟩
    have h1 := card_le_card hsub
    rw [card_sdiff_of_subset hDC, card_filter_mem_sym2, card_filter_mem_sym2, card_D ha hn,
      Nat.choose_self, card_C hn] at h1
    rw [card_C hn]
    have h2 := two_mul_choose_two (2 * a)
    have h3 : 2 * a * (2 * a - 1) + 2 * a = 2 * a * (2 * a) := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h4 : 1 ≤ (2 * a).choose 2 := by
      have : 2 * 1 ≤ 2 * a * (2 * a - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have h5 : 2 * a * (2 * a) = 2 * (a * (2 * a)) := by ring
    omega

/-- **Lemma 4.1.** `G₀` is `a`-sparse. -/
theorem example_sparse (ha : 2 ≤ a) (hn : 2 * a ≤ n) : Sparse a (G0 a n) := by
  intro X hX
  have hWC : W a n ⊆ C a n := sdiff_subset
  -- every edge of `G₀` inside `X` lies inside `X ∩ C` or joins `X ∩ A` to `X \ C`
  have hsub : eIn (G0 a n) X ⊆ eIn (G0 a n) (X ∩ C a n) ∪
      ((X ∩ A a n) ×ˢ (X \ C a n)).image Sym2.mk.uncurry := by
    intro e he
    have he' := he
    simp only [eIn, G0, mem_filter] at he'
    obtain ⟨⟨-, hcond⟩, heX⟩ := he'
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Finset.mk_mem_sym2_iff, mem_compl] at hcond heX
      rw [mem_union]
      by_cases hu : u ∈ C a n <;> by_cases hv : v ∈ C a n
      · left
        simp only [eIn, mem_filter] at he ⊢
        exact ⟨he.1, Finset.mk_mem_sym2_iff.2 ⟨mem_inter.2 ⟨heX.1, hu⟩, mem_inter.2 ⟨heX.2, hv⟩⟩⟩
      · have huA : u ∈ A a n := by
          rcases hcond with h | h
          · by_contra huA; exact h ⟨huA, fun hvA => hv (A_sub_C hvA)⟩
          · exact absurd (hWC h.1.2) hv
        right
        exact mem_image.2 ⟨(u, v), mem_product.2 ⟨mem_inter.2 ⟨heX.1, huA⟩,
          mem_sdiff.2 ⟨heX.2, hv⟩⟩, rfl⟩
      · have hvA : v ∈ A a n := by
          rcases hcond with h | h
          · by_contra hvA; exact h ⟨fun huA => hu (A_sub_C huA), hvA⟩
          · exact absurd (hWC h.1.1) hu
        right
        exact mem_image.2 ⟨(v, u), mem_product.2 ⟨mem_inter.2 ⟨heX.2, hvA⟩,
          mem_sdiff.2 ⟨heX.1, hu⟩⟩, Sym2.eq_swap⟩
      · exfalso
        rcases hcond with h | h
        · exact h ⟨fun h' => hu (A_sub_C h'), fun h' => hv (A_sub_C h')⟩
        · exact hu (hWC h.1.1)
  have hcard : #(eIn (G0 a n) X) ≤ #(eIn (G0 a n) (X ∩ C a n)) + #(X ∩ A a n) * #(X \ C a n) :=
    (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (card_image_le.trans (card_product _ _).le) _))
  have hX12 : #(X ∩ C a n) + #(X \ C a n) = #X := card_inter_add_card_sdiff X (C a n)
  have hA1 : #(X ∩ A a n) ≤ #(X ∩ C a n) := card_le_card (inter_subset_inter_left A_sub_C)
  have hAa : #(X ∩ A a n) ≤ a := (card_le_card inter_subset_right).trans (card_A (by omega)).le
  have hm : a * #(X ∩ C a n) + a * #(X \ C a n) = a * #X := by rw [← mul_add, hX12]
  rcases le_or_gt 2 #(X ∩ C a n) with h1 | h1
  · have hc := core_sparse ha hn inter_subset_right h1
    have : #(X ∩ A a n) * #(X \ C a n) ≤ a * #(X \ C a n) := Nat.mul_le_mul_right _ hAa
    omega
  · have h0 : #(eIn (G0 a n) (X ∩ C a n)) = 0 := by
      have := card_eIn_le (G0 a n) G0_sub_K (X ∩ C a n)
      interval_cases h : #(X ∩ C a n) <;> simp_all
    interval_cases h : #(X ∩ C a n)
    · have : #(X ∩ A a n) = 0 := by omega
      rw [this, zero_mul] at hcard
      nlinarith
    · have : #(X ∩ A a n) * #(X \ C a n) ≤ 1 * #(X \ C a n) := Nat.mul_le_mul_right _ hA1
      nlinarith

/-- **Theorem 1.1, (a) ⟺ (b)**, in terms of sparse sets: for `a ≥ 2` and `n ≥ 2a`, a set of
edges of `K_n` is a maximal `a`-sparse set if and only if it is `a`-sparse with `a(n-1)-1`
edges. -/
theorem maximal_iff (ha : 2 ≤ a) (hn : 2 * a ≤ n) (E : Finset (Sym2 (Fin n))) (hE : E ⊆ K) :
    MaxSparse a E ↔ Sparse a E ∧ #E + a + 1 = a * n := by
  constructor
  · intro hM
    have h1 := card_le_of_maximal hM G0_sub_K (example_sparse ha hn)
    have h2 := card_le_of_sparse hM.2.1 (by rw [Fintype.card_fin]; omega)
    have h3 := card_G0 ha hn
    rw [Fintype.card_fin] at h2
    exact ⟨hM.2.1, by omega⟩
  · rintro ⟨hs, hc⟩
    refine ⟨hE, hs, fun e _ heE hs' => ?_⟩
    have := card_le_of_sparse hs' (by rw [Fintype.card_fin]; omega)
    rw [card_insert_of_notMem heE, Fintype.card_fin] at this
    omega

/-- **Conjecture 1 (Wang–Tian)**, after Lemma 2.1: for `k ≥ 1` and `n ≥ 2k+2`, every maximal
`(k+1)`-sparse set of edges of `K_n` has exactly `(k+1)(n-1)-1` edges. -/
theorem conjecture (k : ℕ) (hk : 1 ≤ k) (hn : 2 * k + 2 ≤ n) (E : Finset (Sym2 (Fin n)))
    (hM : MaxSparse (k + 1) E) : #E = (k + 1) * (n - 1) - 1 := by
  have h := ((maximal_iff (by omega) (by omega) E hM.1).1 hM).2
  have : (k + 1) * n = (k + 1) * (n - 1) + (k + 1) := by
    rw [← Nat.mul_succ]; congr 1; omega
  omega

end Example

end TauMaximal

#print axioms TauMaximal.maximal_iff
#print axioms TauMaximal.conjecture
