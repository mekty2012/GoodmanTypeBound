import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Kruskal intervals (`paper.pdf`, proof of Lemma 4.2)

Fix a total order on the unordered pairs of vertices (`ord`, an injection into
`ℕ`).  For an edge set `F`, the closed edges `B(F)` are the edges of `E` outside
`F` whose endpoints are joined by a path of edges of `F` preceding them.

Kruskal's scan accepts an edge of `A` exactly when it closes no path of
previously accepted edges; we use the equivalent one-shot description
`kruskal A = {e ∈ A | e closes no path of A_{<e}}`.

* `isForest_kruskal`: the accepted edges form a forest;
* `kruskal_eq_of_mem_interval`: for a forest `F`, every `A` with
  `F ⊆ A ⊆ F ∪ B(F)` has `kruskal A = F`;
* `sum_powerset_eq_sum_forests`: hence the intervals `[F, F ∪ B(F)]`, `F` a
  forest in `E`, partition the subsets of `E`.
-/

open Finset SimpleGraph

namespace Taeyoung.Paper.Eventual

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge order: a fixed injective labelling of the unordered pairs. -/
noncomputable def ord (e : Sym2 V) : ℕ := (Fintype.equivFin (Sym2 V) e : ℕ)

lemma ord_injective : Function.Injective (ord (V := V)) := by
  intro e f h
  exact (Fintype.equivFin (Sym2 V)).injective (Fin.ext h)

lemma ord_lt_card (e : Sym2 V) : ord e < Fintype.card (Sym2 V) :=
  (Fintype.equivFin (Sym2 V) e).isLt

/-- The graph with edge set `S`. -/
abbrev graphOf (S : Finset (Sym2 V)) : SimpleGraph V := fromEdgeSet (S : Set (Sym2 V))

lemma graphOf_adj {S : Finset (Sym2 V)} {u v : V} :
    (graphOf S).Adj u v ↔ s(u, v) ∈ S ∧ u ≠ v := by
  simp [graphOf, fromEdgeSet_adj]

lemma graphOf_mono {S T : Finset (Sym2 V)} (h : S ⊆ T) : graphOf S ≤ graphOf T :=
  fromEdgeSet_mono (by exact_mod_cast h)

lemma reachable_mono {S T : Finset (Sym2 V)} (h : S ⊆ T) {u v : V}
    (hr : (graphOf S).Reachable u v) : (graphOf T).Reachable u v :=
  hr.mono (graphOf_mono h)

/-- `e` closes a path of `S`: its endpoints are connected by edges of `S`. -/
def Closes (S : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  ∀ u v, e = s(u, v) → (graphOf S).Reachable u v

lemma closes_mk {S : Finset (Sym2 V)} {u v : V} :
    Closes S s(u, v) ↔ (graphOf S).Reachable u v := by
  constructor
  · intro h; exact h u v rfl
  · intro h a b hab
    rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm

lemma Closes.mono {S T : Finset (Sym2 V)} (h : S ⊆ T) {e : Sym2 V} (he : Closes S e) :
    Closes T e := fun u v huv ↦ reachable_mono h (he u v huv)

/-- A pair closes `S` when it is a non-diagonal edge of `S`. -/
lemma closes_of_mem {S : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ S) : Closes S e := by
  intro u v huv
  subst huv
  by_cases h : u = v
  · subst h; rfl
  · exact (graphOf_adj.mpr ⟨he, h⟩).reachable

/-- If every edge of `S` closes `T`, then `S`-reachability implies `T`-reachability. -/
lemma reachable_of_forall_closes {S T : Finset (Sym2 V)} (h : ∀ f ∈ S, Closes T f)
    {u v : V} (hr : (graphOf S).Reachable u v) : (graphOf T).Reachable u v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons hadj p ih =>
    exact (closes_mk.mp (h _ (graphOf_adj.mp hadj).1)).trans ih

/-- The edges of `S` preceding the threshold `t`. -/
noncomputable def below (S : Finset (Sym2 V)) (t : ℕ) : Finset (Sym2 V) :=
  S.filter fun f ↦ ord f < t

lemma mem_below {S : Finset (Sym2 V)} {t : ℕ} {f : Sym2 V} :
    f ∈ below S t ↔ f ∈ S ∧ ord f < t := Finset.mem_filter

lemma below_subset (S : Finset (Sym2 V)) (t : ℕ) : below S t ⊆ S := Finset.filter_subset _ _

lemma below_mono {S T : Finset (Sym2 V)} (h : S ⊆ T) (t : ℕ) : below S t ⊆ below T t :=
  Finset.filter_subset_filter _ h

lemma below_mono_right (S : Finset (Sym2 V)) {s t : ℕ} (h : s ≤ t) : below S s ⊆ below S t :=
  fun _ hf ↦ mem_below.mpr ⟨(mem_below.mp hf).1, (mem_below.mp hf).2.trans_le h⟩

lemma below_card (S : Finset (Sym2 V)) : below S (Fintype.card (Sym2 V)) = S :=
  Finset.filter_true_of_mem fun f _ ↦ ord_lt_card f

open scoped Classical in
/-- **Kruskal's forest**: the edges of `A` closing no path of earlier edges of `A`. -/
noncomputable def kruskal (A : Finset (Sym2 V)) : Finset (Sym2 V) :=
  A.filter fun e ↦ ¬ Closes (below A (ord e)) e

open scoped Classical in
/-- The closed edges `B(F)`: edges of `E` outside `F` closing a path of `F` of
earlier edges. -/
noncomputable def closedEdges (E F : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter fun e ↦ e ∉ F ∧ Closes (below F (ord e)) e

/-- An edge set is a forest when the graph it spans is acyclic. -/
def IsForest (F : Finset (Sym2 V)) : Prop := (graphOf F).IsAcyclic

open scoped Classical in
/-- The forests contained in `E`. -/
noncomputable def forests (E : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) :=
  E.powerset.filter IsForest

lemma mem_kruskal {A : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ kruskal A ↔ e ∈ A ∧ ¬ Closes (below A (ord e)) e := by
  classical
  unfold kruskal
  rw [Finset.mem_filter]

lemma mem_closedEdges {E F : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ closedEdges E F ↔ e ∈ E ∧ e ∉ F ∧ Closes (below F (ord e)) e := by
  classical
  unfold closedEdges
  rw [Finset.mem_filter]

lemma mem_forests {E F : Finset (Sym2 V)} : F ∈ forests E ↔ F ⊆ E ∧ IsForest F := by
  classical
  unfold forests
  rw [Finset.mem_filter, Finset.mem_powerset]

lemma kruskal_subset (A : Finset (Sym2 V)) : kruskal A ⊆ A :=
  fun _ he ↦ (mem_kruskal.mp he).1

lemma closedEdges_subset (E F : Finset (Sym2 V)) : closedEdges E F ⊆ E :=
  fun _ he ↦ (mem_closedEdges.mp he).1

lemma disjoint_closedEdges (E F : Finset (Sym2 V)) : Disjoint F (closedEdges E F) :=
  Finset.disjoint_left.mpr fun _ hF hB ↦ (mem_closedEdges.mp hB).2.1 hF

/-- The accepted edges below any threshold connect what the edges of `A` below
it connect. -/
theorem reachable_below_kruskal (A : Finset (Sym2 V)) :
    ∀ (t : ℕ) {u v : V}, (graphOf (below A t)).Reachable u v →
      (graphOf (below (kruskal A) t)).Reachable u v := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro u v hr
    refine reachable_of_forall_closes (fun f hf ↦ ?_) hr
    obtain ⟨hfA, hft⟩ := mem_below.mp hf
    by_cases hk : f ∈ kruskal A
    · exact closes_of_mem (mem_below.mpr ⟨hk, hft⟩)
    · have hc : Closes (below A (ord f)) f := by
        by_contra hnc
        exact hk (mem_kruskal.mpr ⟨hfA, hnc⟩)
      intro a b hab
      exact reachable_mono (below_mono_right _ hft.le) (ih (ord f) hft (hc a b hab))

lemma closes_below_kruskal_iff (A : Finset (Sym2 V)) (t : ℕ) (e : Sym2 V) :
    Closes (below (kruskal A) t) e ↔ Closes (below A t) e :=
  ⟨Closes.mono (below_mono (kruskal_subset A) t),
    fun h a b hab ↦ reachable_below_kruskal A t (h a b hab)⟩

/-- `below S (t+1)` adds at most the edge labelled `t`. -/
lemma below_succ (S : Finset (Sym2 V)) (t : ℕ) :
    below S (t + 1) = below S t ∪ S.filter (fun f ↦ ord f = t) := by
  ext f
  simp only [mem_below, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ⟨hf, hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
    · exact Or.inl ⟨hf, h⟩
    · exact Or.inr ⟨hf, h⟩
  · rintro (⟨hf, h⟩ | ⟨hf, h⟩)
    · exact ⟨hf, h.trans (Nat.lt_succ_self t)⟩
    · exact ⟨hf, h ▸ Nat.lt_succ_self _⟩

/-- **Kruskal's accepted edges form a forest.** -/
theorem isForest_kruskal (A : Finset (Sym2 V)) : IsForest (kruskal A) := by
  have key : ∀ t, (graphOf (below (kruskal A) t)).IsAcyclic := by
    intro t
    induction t with
    | zero =>
      have : below (kruskal A) 0 = ∅ := by
        ext f; simp [mem_below]
      rw [this]
      simp [graphOf]
    | succ t ih =>
      rw [below_succ]
      by_cases hex : ∃ e ∈ kruskal A, ord e = t
      · obtain ⟨e, heK, het⟩ := hex
        have hfil : (kruskal A).filter (fun f ↦ ord f = t) = {e} := by
          ext f
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨_, hf⟩; exact ord_injective (hf.trans het.symm)
          · rintro rfl; exact ⟨heK, het⟩
        rw [hfil]
        induction e using Sym2.inductionOn with
        | _ a b =>
          have hnc := (mem_kruskal.mp heK).2
          rw [het, ← closes_below_kruskal_iff, closes_mk] at hnc
          have hgraph : graphOf (below (kruskal A) t ∪ {s(a, b)}) =
              graphOf (below (kruskal A) t) ⊔ edge a b := by
            simp only [graphOf, Finset.coe_union, Finset.coe_singleton, fromEdgeSet_union]
            rfl
          rw [hgraph]
          exact ih.sup_edge_of_not_reachable hnc
      · have hfil : (kruskal A).filter (fun f ↦ ord f = t) = ∅ := by
          ext f
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          exact fun hf het ↦ hex ⟨f, hf, het⟩
        rw [hfil, Finset.union_empty]
        exact ih
  have := key (Fintype.card (Sym2 V))
  rwa [below_card] at this

/-- An edge of a forest closes no path of the other edges of the forest. -/
lemma not_closes_of_isForest {F : Finset (Sym2 V)} (hF : IsForest F) {e : Sym2 V}
    (he : e ∈ F) (hnd : ¬ e.IsDiag) {S : Finset (Sym2 V)} (hS : S ⊆ F.erase e) :
    ¬ Closes S e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    intro hc
    have hab : a ≠ b := fun h ↦ hnd (by simp [h])
    have hadj : (graphOf F).Adj a b := graphOf_adj.mpr ⟨he, hab⟩
    have hbr : (graphOf F).IsBridge s(a, b) :=
      isAcyclic_iff_forall_isBridge.mp hF (by simpa using hadj)
    apply (isBridge_iff.mp hbr)
    refine (closes_mk.mp hc).mono fun x y hxy ↦ ?_
    obtain ⟨hxyS, hne⟩ := graphOf_adj.mp hxy
    have hxyF := hS hxyS
    rw [deleteEdges_adj]
    exact ⟨graphOf_adj.mpr ⟨Finset.mem_of_mem_erase hxyF, hne⟩, by
      simpa using Finset.ne_of_mem_erase hxyF⟩

/-- **Every member of a Kruskal interval scans to its forest.** -/
theorem kruskal_eq_of_mem_interval {E F A : Finset (Sym2 V)} (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (hF : IsForest F) (hFE : F ⊆ E) (hFA : F ⊆ A) (hA : A ⊆ F ∪ closedEdges E F) :
    kruskal A = F := by
  ext e
  constructor
  · intro he
    obtain ⟨heA, hnc⟩ := mem_kruskal.mp he
    by_contra heF
    have heB : e ∈ closedEdges E F := by
      rcases Finset.mem_union.mp (hA heA) with h | h
      · exact absurd h heF
      · exact h
    exact hnc ((mem_closedEdges.mp heB).2.2.mono (below_mono hFA _))
  · intro heF
    refine mem_kruskal.mpr ⟨hFA heF, fun hc ↦ ?_⟩
    have hc' : Closes (below F (ord e)) e := by
      intro a b hab
      refine reachable_of_forall_closes (fun f hf ↦ ?_) (hc a b hab)
      obtain ⟨hfA, hfe⟩ := mem_below.mp hf
      rcases Finset.mem_union.mp (hA hfA) with h | h
      · exact closes_of_mem (mem_below.mpr ⟨h, hfe⟩)
      · exact (mem_closedEdges.mp h).2.2.mono (below_mono_right _ hfe.le)
    refine not_closes_of_isForest hF heF (hE e (hFE heF)) (fun f hf ↦ ?_) hc'
    obtain ⟨hfF, hfe⟩ := mem_below.mp hf
    exact Finset.mem_erase.mpr ⟨fun h ↦ (lt_irrefl _) (h ▸ hfe), hfF⟩

lemma subset_kruskal_union {E A : Finset (Sym2 V)} (hAE : A ⊆ E) :
    A ⊆ kruskal A ∪ closedEdges E (kruskal A) := by
  intro e heA
  by_cases hk : e ∈ kruskal A
  · exact Finset.mem_union_left _ hk
  · refine Finset.mem_union_right _ (mem_closedEdges.mpr ⟨hAE heA, hk, ?_⟩)
    rw [closes_below_kruskal_iff]
    by_contra hnc
    exact hk (mem_kruskal.mpr ⟨heA, hnc⟩)

/-- **The Kruskal intervals partition the subsets of `E`.** -/
theorem sum_powerset_eq_sum_forests {M : Type*} [AddCommMonoid M] {E : Finset (Sym2 V)}
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (f : Finset (Sym2 V) → M) :
    ∑ A ∈ E.powerset, f A =
      ∑ F ∈ forests E, ∑ D ∈ (closedEdges E F).powerset, f (F ∪ D) := by
  classical
  have hmaps : ∀ A ∈ E.powerset, kruskal A ∈ forests E := fun A hA ↦
    mem_forests.mpr ⟨(kruskal_subset A).trans (Finset.mem_powerset.mp hA),
      isForest_kruskal A⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun F hF ↦ ?_
  obtain ⟨hFE, hFf⟩ := mem_forests.mp hF
  have hinj : Set.InjOn (fun D ↦ F ∪ D) ((closedEdges E F).powerset : Set _) := by
    intro D₁ h₁ D₂ h₂ h
    have hd₁ : Disjoint F D₁ :=
      (disjoint_closedEdges E F).mono_right (Finset.mem_powerset.mp h₁)
    have hd₂ : Disjoint F D₂ :=
      (disjoint_closedEdges E F).mono_right (Finset.mem_powerset.mp h₂)
    have : (F ∪ D₁) \ F = (F ∪ D₂) \ F := by simp only at h; rw [h]
    rwa [Finset.union_sdiff_cancel_left hd₁, Finset.union_sdiff_cancel_left hd₂] at this
  rw [← Finset.sum_image hinj]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨hAE, rfl⟩
    refine ⟨A \ kruskal A, ?_, Finset.union_sdiff_of_subset (kruskal_subset A)⟩
    intro e he
    obtain ⟨heA, hek⟩ := Finset.mem_sdiff.mp he
    rcases Finset.mem_union.mp (subset_kruskal_union hAE heA) with h | h
    · exact absurd h hek
    · exact h
  · rintro ⟨D, hD, rfl⟩
    have hDE : D ⊆ E := hD.trans (closedEdges_subset E F)
    refine ⟨Finset.union_subset hFE hDE, ?_⟩
    exact kruskal_eq_of_mem_interval hE hFf hFE Finset.subset_union_left
      (Finset.union_subset_union subset_rfl hD)

end Taeyoung.Paper.Eventual
