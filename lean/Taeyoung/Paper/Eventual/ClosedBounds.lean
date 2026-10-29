import Taeyoung.Paper.Eventual.ClosedIntegrals

/-!
# Bounding the closed intervals (`paper.pdf`, Lemma 4.5 and proof of
Proposition 4.12)

* `intervalInt_le_closing`: for `e ∈ B(F)` with closing path `P`,
  `I_F(U) ≤ Δ^{|F \ P|} Q_{|P|+1}`;
* `intervalInt_leading`: for a leading forest (`|F| = g - 1`), `I_F(U) = Q_g`;
* the sum over forests, (4.29), is `sum_intervalInt_le`
  in `ClosedSum.lean`.
-/

open MeasureTheory Finset SimpleGraph

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- Dropping the other closed edges. -/
lemma intervalInt_le_single (U : Graphon Ω μ) {F : Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∈ closedEdges H.edgeFinset F) :
    intervalInt H.edgeFinset U F ≤ wInt (closedKernel U {e}) (F ∪ {e}) (fun _ ↦ BddFun.one) := by
  have heF : e ∉ F := (mem_closedEdges.mp he).2.1
  refine wInt_mono_of_le fun x ↦ ?_
  rw [edgeProd_closedKernel U (disjoint_closedEdges _ F),
    edgeProd_closedKernel U (Finset.disjoint_singleton_right.mpr heF)]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (edgeProd_nonneg _ _ x))
    (Finset.prod_nonneg fun v _ ↦ by simp [BddFun.one])
  · rw [Finset.prod_singleton, ← Finset.mul_prod_erase _ _ he]
    refine mul_le_of_le_one_right (by linarith [edgeValue_le_one U x e]) ?_
    exact Finset.prod_le_one (fun f _ ↦ by linarith [edgeValue_le_one U x f])
      fun f _ ↦ by linarith [edgeValue_nonneg U x f]

/-- The vertices of a closing path are pairwise unjoined by the other edges of `F`. -/
lemma closing_separated {F : Finset (Sym2 V)} (hFE : F ⊆ H.edgeFinset) (hfor : IsForest F)
    {e : Sym2 V} (cp : ClosingPath H F e) :
    ∀ r₁ ∈ cp.p.support.toFinset, ∀ r₂ ∈ cp.p.support.toFinset,
      (graphOf (F \ cp.edgeSet')).Reachable r₁ r₂ → r₁ = r₂ := by
  intro r₁ h₁ r₂ h₂ hr
  by_contra hne
  obtain ⟨q₁, hq₁⟩ := hr.exists_isPath
  -- the closing path joins `r₁` and `r₂` inside `P`
  have hpP : ∀ f ∈ cp.p.edges, f ∈ (graphOf cp.edgeSet').edgeSet := fun f hf ↦
    mem_edgeSet_graphOf.mpr ⟨List.mem_toFinset.mpr hf,
      H.not_isDiag_of_mem_edgeSet (cp.p.edges_subset_edgeSet hf)⟩
  set pP := cp.p.transfer _ hpP
  have hreach : ∀ r ∈ cp.p.support, (graphOf cp.edgeSet').Reachable cp.u r := by
    intro r hr
    have hr' : r ∈ pP.support := by rw [Walk.support_transfer]; exact hr
    exact (pP.takeUntil r hr').reachable
  have hP : (graphOf cp.edgeSet').Reachable r₁ r₂ :=
    (hreach r₁ (List.mem_toFinset.mp h₁)).symm.trans (hreach r₂ (List.mem_toFinset.mp h₂))
  obtain ⟨q₂, hq₂⟩ := hP.exists_isPath
  have hq₁F : ∀ f ∈ q₁.edges, f ∈ (graphOf F).edgeSet := fun f hf ↦ by
    obtain ⟨h1, h2⟩ := mem_edgeSet_graphOf.mp (q₁.edges_subset_edgeSet hf)
    exact mem_edgeSet_graphOf.mpr ⟨(Finset.mem_sdiff.mp h1).1, h2⟩
  have hq₂F : ∀ f ∈ q₂.edges, f ∈ (graphOf F).edgeSet := fun f hf ↦ by
    obtain ⟨h1, h2⟩ := mem_edgeSet_graphOf.mp (q₂.edges_subset_edgeSet hf)
    exact mem_edgeSet_graphOf.mpr ⟨cp.edgeSet'_subset h1, h2⟩
  have huniq := hfor.path_unique ⟨q₁.transfer _ hq₁F, hq₁.transfer hq₁F⟩
    ⟨q₂.transfer _ hq₂F, hq₂.transfer hq₂F⟩
  have hedges := congrArg (fun r : (graphOf F).Path r₁ r₂ ↦ r.1.edges) huniq
  simp only [Walk.edges_transfer] at hedges
  -- the first edge of `q₁` is in `F \ P` and in `P`
  have hnil : ¬ q₁.Nil := Walk.not_nil_of_ne hne
  obtain ⟨f, hf⟩ : ∃ f, f ∈ q₁.edges := by
    cases q₁ with
    | nil => exact absurd Walk.Nil.nil hnil
    | cons h q => exact ⟨_, List.mem_cons.mpr (Or.inl rfl)⟩
  have hf1 := (mem_edgeSet_graphOf.mp (q₁.edges_subset_edgeSet hf)).1
  have hf2 := (mem_edgeSet_graphOf.mp (q₂.edges_subset_edgeSet (hedges ▸ hf))).1
  exact (Finset.mem_sdiff.mp hf1).2 hf2

/-- **The leaf-integration estimate**: `I_F(U) ≤ Δ^{|F \ P|} Q_{|P|+1}`. -/
theorem intervalInt_le_closing (U : Graphon Ω μ) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hdeg : ∀ x, degree U x ≤ Δ) {F : Finset (Sym2 V)} (hFE : F ⊆ H.edgeFinset)
    (hfor : IsForest F) {e : Sym2 V} (he : e ∈ closedEdges H.edgeFinset F)
    (cp : ClosingPath H F e) :
    intervalInt H.edgeFinset U F ≤ Δ ^ (F \ cp.edgeSet').card * Qs U (cp.edgeSet'.card + 1) := by
  refine (intervalInt_le_single U he).trans ?_
  have heF : e ∉ F := (mem_closedEdges.mp he).2.1
  have hnd : ∀ f ∈ F, ¬ f.IsDiag := fun f hf ↦ not_isDiag_of_mem_edgeFinset H f (hFE hf)
  set R := cp.p.support.toFinset
  have hsub : F \ cp.edgeSet' ⊆ F ∪ {e} := Finset.sdiff_subset.trans Finset.subset_union_left
  have hκ : ∀ f ∈ F \ cp.edgeSet', closedKernel U {e} f = U := fun f hf ↦
    closedKernel_of_notMem U (by
      rw [Finset.mem_singleton]; rintro rfl; exact heF (Finset.mem_sdiff.mp hf).1)
  have hdiff : (F ∪ {e}) \ (F \ cp.edgeSet') = cp.edgeSet' ∪ {e} := by
    ext f
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, not_and, not_not]
    constructor
    · rintro ⟨hf | rfl, h⟩
      · exact Or.inl (h hf)
      · exact Or.inr rfl
    · rintro (hf | rfl)
      · exact ⟨Or.inl (cp.edgeSet'_subset hf), fun _ ↦ hf⟩
      · exact ⟨Or.inr rfl, fun h ↦ absurd h heF⟩
  have hout : ∀ f ∈ (F ∪ {e}) \ (F \ cp.edgeSet'), ∀ v ∈ f, v ∈ R := by
    rw [hdiff]
    intro f hf v hv
    rw [List.mem_toFinset]
    rcases Finset.mem_union.mp hf with hf | hf
    · exact Walk.mem_support_of_mem_edges (List.mem_toFinset.mp hf) hv
    · rw [Finset.mem_singleton.mp hf, cp.e_eq] at hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact cp.p.start_mem_support
      · exact cp.p.end_mem_support
  have hprune := wInt_prune U hΔ0 hdeg (closedKernel U {e}) R _ (F ∪ {e}) (F \ cp.edgeSet') rfl
    hsub hκ (hfor.subset Finset.sdiff_subset)
    (fun f hf ↦ hnd f (Finset.mem_sdiff.mp hf).1) (closing_separated hFE hfor cp) hout
    (fun _ ↦ BddFun.one) (fun _ ↦ 1) (fun _ _ ↦ zero_le_one) (fun _ ↦ zero_le_one)
    (fun _ _ _ ↦ le_rfl)
  rw [hdiff, Finset.prod_const_one, mul_one] at hprune
  have hw : wInt (closedKernel U {e}) (cp.edgeSet' ∪ {e})
      (fun v ↦ if v ∈ R then BddFun.one else BddFun.one) =
      wInt (closedKernel U {e}) (cp.edgeSet' ∪ {e}) (fun _ ↦ BddFun.one) := by
    apply wInt_congr_weight; intro v y; split_ifs <;> rfl
  rw [hw] at hprune
  refine hprune.trans (le_of_eq ?_)
  congr 1
  have hlen : cp.p.length = (cp.p.length - 1) + 1 := by
    have := cp.isPath
    have : 1 ≤ cp.p.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne cp.ne)
    omega
  rw [wInt_closingPath cp U hlen, cp.card_edgeSet']
  congr 1
  omega

/-- **The leading forests**: `I_F(U) = Q_g`. -/
theorem intervalInt_leading (U : Graphon Ω μ) {F : Finset (Sym2 V)} (hF : F ∈ leadingForests H) :
    intervalInt H.edgeFinset U F = Qs U H.girth := by
  obtain ⟨hFf, hB, hcard⟩ := mem_leadingForests.mp hF
  have hFE := (mem_forests.mp hFf).1
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hB
  have hsing := closedEdges_eq_singleton hFE hcard he
  obtain ⟨cp⟩ := exists_closingPath hFE he
  have heE := (mem_closedEdges.mp he).1
  have hPF : cp.edgeSet' = F := by
    refine Finset.eq_of_subset_of_card_le cp.edgeSet'_subset ?_
    have := cp.girth_le heE
    rw [cp.card_edgeSet']; omega
  unfold intervalInt
  rw [hsing]
  rw [← hPF]
  have hlen : cp.p.length = (cp.p.length - 1) + 1 := by
    have : 1 ≤ cp.p.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne cp.ne)
    omega
  rw [wInt_closingPath cp U hlen]
  congr 1
  have hc : cp.p.length = F.card := by rw [← cp.card_edgeSet', hPF]
  omega

end Taeyoung.Paper.Eventual
