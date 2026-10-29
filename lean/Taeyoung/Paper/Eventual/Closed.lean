import Taeyoung.Paper.Eventual.Cycles

/-!
# Forests with closed edges (`paper.pdf`, proof of Proposition 4.12)

Let `H` have girth `g`, `E = E(H)`, and let `F ⊆ E` be a forest.

* `ClosingPath`: an edge `e ∈ B(F)` closes a path of earlier edges of `F`;
  together with `e` it is a cycle of `H` (`ClosingPath.isCycle`), so
  `g ≤ |F| + 1` whenever `B(F) ≠ ∅` (`girth_le_card_add_one`).
* `closedEdges_eq_singleton`: if moreover `|F| = g - 1`, then `F` is that path
  and `B(F)` is the single closing edge.
* `leading_of_cycleSet`: conversely, a shortest cycle with its largest edge
  deleted is such a forest; `card_cycleSets_le_card_leading` counts them.
-/

open Finset SimpleGraph

namespace Taeyoung.Paper.Eventual

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Segments of paths -/

/-- The segment of a path between positions `i ≤ j`. -/
noncomputable def pathSegment {G : SimpleGraph V} {u v : V} (p : G.Walk u v) {i j : ℕ}
    (hij : i ≤ j) : G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j - i)).copy rfl (by rw [Walk.drop_getVert]; congr 1; omega)

lemma pathSegment_length {G : SimpleGraph V} {u v : V} (p : G.Walk u v) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p.length) : (pathSegment p hij).length = j - i := by
  rw [pathSegment, Walk.length_copy, Walk.take_length, Walk.drop_length]; omega

lemma pathSegment_getVert {G : SimpleGraph V} {u v : V} (p : G.Walk u v) {i j k : ℕ}
    (hij : i ≤ j) (hk : k ≤ j - i) : (pathSegment p hij).getVert k = p.getVert (i + k) := by
  rw [pathSegment, Walk.getVert_copy, Walk.take_getVert, Walk.drop_getVert, min_eq_right hk]

lemma pathSegment_isPath {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) : (pathSegment p hij).IsPath := by
  rw [← Walk.IsPath.getVert_injOn_iff]
  intro a ha b hb hab
  simp only [Set.mem_setOf_eq, pathSegment_length p hij hj] at ha hb
  rw [pathSegment_getVert p hij ha, pathSegment_getVert p hij hb] at hab
  have := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) hab
  omega

lemma pathSegment_edges_subset {G : SimpleGraph V} {u v : V} (p : G.Walk u v) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p.length) : ∀ f ∈ (pathSegment p hij).edges, f ∈ p.edges := by
  intro f hf
  rw [edges_eq_map_getVert, pathSegment_length p hij hj] at hf
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hf
  have hk' := List.mem_range.mp hk
  rw [pathSegment_getVert p hij (by omega), pathSegment_getVert p hij (by omega),
    edges_eq_map_getVert]
  exact List.mem_map.mpr ⟨i + k, List.mem_range.mpr (by omega), by rw [Nat.add_assoc]⟩

/-! ### Closing paths -/

variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- A path of earlier edges of `F` joining the ends of `e`. -/
structure ClosingPath (F : Finset (Sym2 V)) (e : Sym2 V) where
  u : V
  v : V
  p : H.Walk u v
  e_eq : e = s(u, v)
  ne : u ≠ v
  isPath : p.IsPath
  edges_mem : ∀ f ∈ p.edges, f ∈ F ∧ ord f < ord e

variable {H}

theorem exists_closingPath {F : Finset (Sym2 V)} (hFE : F ⊆ H.edgeFinset) {e : Sym2 V}
    (he : e ∈ closedEdges H.edgeFinset F) : Nonempty (ClosingPath H F e) := by
  obtain ⟨heE, -, hc⟩ := mem_closedEdges.mp he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv : u ≠ v := fun h ↦ (SimpleGraph.not_isDiag_of_mem_edgeSet H
      (SimpleGraph.mem_edgeFinset.mp heE)) (by simp [h])
    obtain ⟨p0, hp0⟩ := (closes_mk.mp hc).exists_isPath
    have hmem : ∀ f ∈ p0.edges, f ∈ F ∧ ord f < ord s(u, v) := fun f hf ↦
      mem_below.mp (mem_edgeSet_graphOf.mp (p0.edges_subset_edgeSet hf)).1
    have hH : ∀ f ∈ p0.edges, f ∈ H.edgeSet := fun f hf ↦
      SimpleGraph.mem_edgeFinset.mp (hFE (hmem f hf).1)
    exact ⟨⟨u, v, p0.transfer H hH, rfl, huv, hp0.transfer hH, by
      rw [Walk.edges_transfer]; exact hmem⟩⟩

namespace ClosingPath

variable {F : Finset (Sym2 V)} {e : Sym2 V} (cp : ClosingPath H F e)

lemma adj (heE : e ∈ H.edgeFinset) : H.Adj cp.v cp.u := by
  have := SimpleGraph.mem_edgeFinset.mp heE
  rw [cp.e_eq] at this
  exact (H.mem_edgeSet.mp this).symm

lemma mk_notMem_edges : s(cp.u, cp.v) ∉ cp.p.edges := fun h ↦ by
  have := (cp.edges_mem _ h).2
  rw [← cp.e_eq] at this
  exact lt_irrefl _ this

lemma e_notMem_edges : e ∉ cp.p.edges := fun h ↦ lt_irrefl _ (cp.edges_mem e h).2

/-- A closing path with its closing edge is a cycle. -/
lemma isCycle (heE : e ∈ H.edgeFinset) : (Walk.cons (cp.adj heE) cp.p).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨cp.isPath, fun h ↦ cp.mk_notMem_edges ?_⟩
  rwa [Sym2.eq_swap]

lemma girth_le (heE : e ∈ H.edgeFinset) : H.girth ≤ cp.p.length + 1 := by
  have := H.girth_le_length (cp.isCycle heE)
  rwa [Walk.length_cons] at this

/-- The edge set of the closing path. -/
def edgeSet' : Finset (Sym2 V) := cp.p.edges.toFinset

lemma edgeSet'_subset : cp.edgeSet' ⊆ F := fun f hf ↦ (cp.edges_mem f (List.mem_toFinset.mp hf)).1

lemma card_edgeSet' : cp.edgeSet'.card = cp.p.length := card_edges_toFinset cp.isPath

lemma e_notMem_edgeSet' : e ∉ cp.edgeSet' := fun h ↦ cp.e_notMem_edges (List.mem_toFinset.mp h)

/-- The closing path and its edge form an edge set of a cycle of length `|P| + 1`. -/
lemma insert_mem_cycleSets (heE : e ∈ H.edgeFinset) :
    insert e cp.edgeSet' ∈ cycleSets H (cp.edgeSet'.card + 1) := by
  refine Taeyoung.Paper.Eventual.mem_cycleSets.mpr ⟨?_, by rw [Finset.card_insert_of_notMem cp.e_notMem_edgeSet'], ?_⟩
  · refine Finset.insert_subset heE fun f hf ↦ ?_
    exact SimpleGraph.mem_edgeFinset.mpr (cp.p.edges_subset_edgeSet (List.mem_toFinset.mp hf))
  · refine ⟨cp.v, Walk.cons (cp.adj heE) cp.p, cp.isCycle heE, ?_⟩
    rw [Walk.edges_cons, List.toFinset_cons, ← cp.e_eq.trans (Sym2.eq_swap)]
    rfl

end ClosingPath

/-- **A closed edge forces `|F| ≥ g - 1`.** -/
theorem girth_le_card_add_one {F : Finset (Sym2 V)} (hFE : F ⊆ H.edgeFinset)
    (hB : closedEdges H.edgeFinset F ≠ ∅) : H.girth ≤ F.card + 1 := by
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hB
  obtain ⟨cp⟩ := exists_closingPath hFE he
  have h1 := cp.girth_le (mem_closedEdges.mp he).1
  have h2 := Finset.card_le_card cp.edgeSet'_subset
  rw [cp.card_edgeSet'] at h2
  omega

/-- The vertices of an edge set's edges, for a path through all of them. -/
lemma mem_support_of_edges {u v a x : V} {p : H.Walk u v} {q : H.Walk a x}
    (hq : ¬ q.Nil) (hsub : ∀ f ∈ q.edges, f ∈ p.edges) : a ∈ p.support := by
  cases q with
  | nil => exact absurd Walk.Nil.nil hq
  | @cons _ b _ h q' =>
    have hmem : s(a, b) ∈ (Walk.cons h q').edges := by
      rw [Walk.edges_cons]; exact List.mem_cons.mpr (Or.inl rfl)
    exact p.fst_mem_support_of_mem_edges (hsub _ hmem)

/-- **The leading forests.**  If `|F| = g - 1` and `e ∈ B(F)`, then `B(F) = {e}`. -/
theorem closedEdges_eq_singleton {F : Finset (Sym2 V)} (hFE : F ⊆ H.edgeFinset)
    (hcard : F.card + 1 = H.girth) {e : Sym2 V} (he : e ∈ closedEdges H.edgeFinset F) :
    closedEdges H.edgeFinset F = {e} := by
  obtain ⟨cp⟩ := exists_closingPath hFE he
  have heE := (mem_closedEdges.mp he).1
  have hPF : cp.edgeSet' = F := by
    refine Finset.eq_of_subset_of_card_le cp.edgeSet'_subset ?_
    have := cp.girth_le heE
    rw [cp.card_edgeSet']; omega
  have hL : cp.p.length + 1 = H.girth := by
    rw [← cp.card_edgeSet', hPF, hcard]
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨he, fun e' he' ↦ ?_⟩
  obtain ⟨cp'⟩ := exists_closingPath hFE he'
  obtain ⟨he'E, he'F, -⟩ := mem_closedEdges.mp he'
  have hsub : ∀ f ∈ cp'.p.edges, f ∈ cp.p.edges := fun f hf ↦ by
    have := (cp'.edges_mem f hf).1
    rw [← hPF] at this
    exact List.mem_toFinset.mp this
  have hnil : ¬ cp'.p.Nil := Walk.not_nil_of_ne cp'.ne
  have ha : cp'.u ∈ cp.p.support := mem_support_of_edges hnil hsub
  have hb : cp'.v ∈ cp.p.support := by
    refine mem_support_of_edges (q := cp'.p.reverse) (by simpa using hnil) fun f hf ↦ ?_
    exact hsub f (by simpa using hf)
  obtain ⟨i, hi, hiL⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  obtain ⟨j, hj, hjL⟩ := Walk.mem_support_iff_exists_getVert.mp hb
  have hij : i ≠ j := fun h ↦ cp'.ne (by rw [← hi, ← hj, h])
  -- the segment of the closing path between the ends of `e'`, closed by `e'`
  have key : ∀ i j, i < j → j ≤ cp.p.length →
      (cp.p.getVert i = cp'.u ∧ cp.p.getVert j = cp'.v ∨
        cp.p.getVert i = cp'.v ∧ cp.p.getVert j = cp'.u) →
      i = 0 ∧ j = cp.p.length := by
    intro i j hlt hjL hends
    have h2 : H.Adj cp'.u cp'.v := by
      have h1 := SimpleGraph.mem_edgeFinset.mp he'E
      rw [cp'.e_eq] at h1
      exact H.mem_edgeSet.mp h1
    have hadj : H.Adj (cp.p.getVert j) (cp.p.getVert i) := by
      rcases hends with ⟨hi', hj'⟩ | ⟨hi', hj'⟩
      · rw [hi', hj']; exact h2.symm
      · rw [hi', hj']; exact h2
    have he'eq : s(cp.p.getVert j, cp.p.getVert i) = e' := by
      rw [cp'.e_eq]
      rcases hends with ⟨hi', hj'⟩ | ⟨hi', hj'⟩
      · rw [hi', hj', Sym2.eq_swap]
      · rw [hi', hj']
    have hseg := pathSegment_isPath cp.isPath hlt.le hjL
    have hcyc : (Walk.cons hadj (pathSegment cp.p hlt.le)).IsCycle := by
      rw [Walk.cons_isCycle_iff]
      refine ⟨hseg, fun h ↦ he'F ?_⟩
      have hmem := pathSegment_edges_subset cp.p hlt.le hjL _ h
      have hmem' : s(cp.p.getVert j, cp.p.getVert i) ∈ cp.edgeSet' := List.mem_toFinset.mpr hmem
      rw [hPF, he'eq] at hmem'
      exact hmem'
    have := H.girth_le_length hcyc
    rw [Walk.length_cons, pathSegment_length cp.p hlt.le hjL] at this
    omega
  have hends : (cp'.u = cp.u ∧ cp'.v = cp.v) ∨ (cp'.u = cp.v ∧ cp'.v = cp.u) := by
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · obtain ⟨h0, hL'⟩ := key i j hlt hjL (Or.inl ⟨hi, hj⟩)
      left
      exact ⟨by rw [← hi, h0, Walk.getVert_zero], by rw [← hj, hL', Walk.getVert_length]⟩
    · obtain ⟨h0, hL'⟩ := key j i hlt hiL (Or.inr ⟨hj, hi⟩)
      right
      exact ⟨by rw [← hi, hL', Walk.getVert_length], by rw [← hj, h0, Walk.getVert_zero]⟩
  rw [cp'.e_eq, cp.e_eq]
  rcases hends with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [hu, hv]
  · rw [hu, hv, Sym2.eq_swap]

/-! ### Shortest cycles give leading forests -/

/-- The largest edge of a nonempty edge set. -/
noncomputable def topEdge (C : Finset (Sym2 V)) (hC : C.Nonempty) : Sym2 V :=
  (C.exists_max_image ord hC).choose

lemma topEdge_mem (C : Finset (Sym2 V)) (hC : C.Nonempty) : topEdge C hC ∈ C :=
  (C.exists_max_image ord hC).choose_spec.1

lemma ord_le_topEdge (C : Finset (Sym2 V)) (hC : C.Nonempty) {f : Sym2 V} (hf : f ∈ C) :
    ord f ≤ ord (topEdge C hC) :=
  (C.exists_max_image ord hC).choose_spec.2 f hf

open scoped Classical in
/-- The forests `F ⊆ E` with `B(F) ≠ ∅` and `|F| = g - 1`. -/
noncomputable def leadingForests (H : SimpleGraph V) [DecidableRel H.Adj] :
    Finset (Finset (Sym2 V)) :=
  (forests H.edgeFinset).filter fun F ↦
    closedEdges H.edgeFinset F ≠ ∅ ∧ F.card + 1 = H.girth

lemma mem_leadingForests {F : Finset (Sym2 V)} :
    F ∈ leadingForests H ↔ F ∈ forests H.edgeFinset ∧ closedEdges H.edgeFinset F ≠ ∅ ∧
      F.card + 1 = H.girth := by
  classical
  unfold leadingForests
  rw [Finset.mem_filter]

/-- A shortest cycle with its largest edge deleted is a leading forest, closed by that
edge. -/
theorem leading_of_cycleSet {C : Finset (Sym2 V)} (hC : C ∈ cycleSets H H.girth)
    (hne : C.Nonempty) :
    C.erase (topEdge C hne) ∈ leadingForests H ∧
      topEdge C hne ∈ closedEdges H.edgeFinset (C.erase (topEdge C hne)) := by
  classical
  obtain ⟨hCE, hCcard, w, c, hc, hcC⟩ := mem_cycleSets.mp hC
  set e := topEdge C hne
  have heC : e ∈ C := topEdge_mem C hne
  set F := C.erase e with hF
  have hFE : F ⊆ H.edgeFinset := (Finset.erase_subset _ _).trans hCE
  have hFcard : F.card + 1 = H.girth := by
    rw [hF, Finset.card_erase_of_mem heC, hCcard]
    have := hc.three_le_length
    have h3 : 3 ≤ C.card := by rw [← hcC, ← length_eq_card_of_cycle hc]; exact this
    omega
  -- `F` is a forest: its cycles would be shorter than the girth
  have hfor : IsForest F := by
    intro x c' hc'
    have hH : ∀ f ∈ c'.edges, f ∈ H.edgeSet := fun f hf ↦ SimpleGraph.mem_edgeFinset.mp
      (hFE (mem_edgeSet_graphOf.mp (c'.edges_subset_edgeSet hf)).1)
    have h1 := H.girth_le_length (hc'.transfer hH)
    rw [Walk.length_transfer, length_eq_card_of_cycle hc'] at h1
    have h2 := Finset.card_le_card (edges_toFinset_subset_graphOf c')
    omega
  -- the top edge closes the rest of the cycle
  have hbelow : below F (ord e) = F := by
    refine Finset.filter_true_of_mem fun f hf ↦ ?_
    have hfC := Finset.mem_of_mem_erase hf
    have hfe := Finset.ne_of_mem_erase hf
    exact lt_of_le_of_ne (ord_le_topEdge C hne hfC) fun h ↦ hfe (ord_injective h)
  have hclose : Closes (below F (ord e)) e := by
    rw [hbelow]
    intro a b hab
    have hcC' : ∀ f ∈ c.edges, f ∈ (graphOf C).edgeSet := fun f hf ↦
      mem_edgeSet_graphOf.mpr ⟨hcC ▸ List.mem_toFinset.mpr hf,
        H.not_isDiag_of_mem_edgeSet (c.edges_subset_edgeSet hf)⟩
    have hea : s(a, b) ∈ (c.transfer _ hcC').edges := by
      rw [Walk.edges_transfer, ← hab]; exact List.mem_toFinset.mp (hcC ▸ heC)
    obtain ⟨-, hr⟩ := adj_and_reachable_delete_edges_iff_exists_cycle.mpr
      ⟨w, c.transfer _ hcC', hc.transfer hcC', hea⟩
    refine hr.mono fun x y hxy ↦ ?_
    rw [deleteEdges_adj] at hxy
    obtain ⟨hxy1, hxy2⟩ := hxy
    obtain ⟨hxyC, hne'⟩ := graphOf_adj.mp hxy1
    refine graphOf_adj.mpr ⟨Finset.mem_erase.mpr ⟨fun h ↦ hxy2 ?_, hxyC⟩, hne'⟩
    rw [h, hab]; rfl
  have heB : e ∈ closedEdges H.edgeFinset F :=
    mem_closedEdges.mpr ⟨hCE heC, Finset.notMem_erase e C, hclose⟩
  refine ⟨?_, heB⟩
  unfold leadingForests
  rw [Finset.mem_filter]
  exact ⟨mem_forests.mpr ⟨hFE, hfor⟩, Finset.ne_empty_of_mem heB, hFcard⟩

/-- **There are at least as many leading forests as shortest cycles.** -/
theorem card_cycleSets_le_card_leading :
    (cycleSets H H.girth).card ≤ (leadingForests H).card := by
  classical
  by_cases hac : H.IsAcyclic
  · -- no cycles at all
    have : cycleSets H H.girth = ∅ := by
      ext C
      simp only [Finset.notMem_empty, iff_false]
      intro hC
      obtain ⟨-, -, w, c, hc, -⟩ := mem_cycleSets.mp hC
      exact hac c hc
    rw [this]; exact Nat.zero_le _
  have hnonempty : ∀ C ∈ cycleSets H H.girth, C.Nonempty := by
    intro C hC
    obtain ⟨-, hcard, -⟩ := mem_cycleSets.mp hC
    have := three_le_girth hac
    exact Finset.card_pos.mp (by omega)
  let f : Finset (Sym2 V) → Finset (Sym2 V) := fun C ↦
    if hC : C.Nonempty then C.erase (topEdge C hC) else ∅
  refine Finset.card_le_card_of_injOn f (fun C hC ↦ ?_) (fun C hC C' hC' hff ↦ ?_)
  · have hne := hnonempty C hC
    simp only [f, dif_pos hne]
    exact (leading_of_cycleSet hC hne).1
  · have hne := hnonempty C hC
    have hne' := hnonempty C' hC'
    simp only [f, dif_pos hne, dif_pos hne'] at hff
    obtain ⟨hL, hB⟩ := leading_of_cycleSet hC hne
    obtain ⟨hL', hB'⟩ := leading_of_cycleSet hC' hne'
    have hFE : C.erase (topEdge C hne) ⊆ H.edgeFinset :=
      (mem_forests.mp (Finset.mem_filter.mp hL).1).1
    have hcard := (Finset.mem_filter.mp hL).2.2
    have hsing := closedEdges_eq_singleton hFE hcard hB
    rw [hff] at hsing
    have htop : topEdge C' hne' = topEdge C hne := by
      rw [hsing] at hB'
      exact Finset.mem_singleton.mp hB'
    have h1 := Finset.insert_erase (topEdge_mem C hne)
    have h2 := Finset.insert_erase (topEdge_mem C' hne')
    rw [← h1, ← h2, hff, htop]

end Taeyoung.Paper.Eventual
