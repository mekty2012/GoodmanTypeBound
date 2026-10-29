import Taeyoung.Paper.Eventual.ClosedBounds

/-!
# Summing the closed intervals (`paper.pdf`, (4.29))

Group the forests `F` with a closed edge and `|F| ≥ g` by the cycle formed by a
closed edge `e` and its closing path `P` (the largest edge of the cycle is `e`),
and by the remaining edges `F \ P`.  This map is injective, so

`∑ I_F(U) ≤ ∑_{s ≤ n} c_s · w_s · Q_s`,  `w_g = (1+Δ)^m - 1`, `w_s = (1+Δ)^m` (`s > g`),

where `c_s` counts the edge sets of `s`-cycles (`sum_intervalInt_le`).
-/

open MeasureTheory Finset SimpleGraph

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- A cycle has at most `n` edges. -/
lemma card_le_of_mem_cycleSets {s : ℕ} {C : Finset (Sym2 V)} (hC : C ∈ cycleSets H s) :
    C.card ≤ Fintype.card V := by
  obtain ⟨-, -, w, c, hc, rfl⟩ := mem_cycleSets.mp hC
  rw [← length_eq_card_of_cycle hc]
  have h1 := hc.support_nodup.length_le_card
  rw [List.length_tail, Walk.length_support] at h1
  omega

/-- `∑_{R ⊆ E} Δ^{|R|} = (1+Δ)^m`. -/
lemma sum_powerset_pow (E : Finset (Sym2 V)) (Δ : ℝ) :
    ∑ R ∈ E.powerset, Δ ^ R.card = (1 + Δ) ^ E.card := by
  have := Finset.prod_add (fun _ ↦ Δ) (fun _ ↦ (1 : ℝ)) E
  simp only [Finset.prod_const, one_pow, mul_one] at this
  rw [add_comm, ← this]

open scoped Classical in
/-- The data attached to a forest with a closed edge: the cycle `P ∪ {e}` and `F \ P`. -/
noncomputable def cycleData (H : SimpleGraph V) [DecidableRel H.Adj] (F : Finset (Sym2 V)) :
    Finset (Sym2 V) × Finset (Sym2 V) :=
  if h : F ⊆ H.edgeFinset ∧ closedEdges H.edgeFinset F ≠ ∅ then
    (insert (Finset.nonempty_iff_ne_empty.mpr h.2).choose
        (exists_closingPath h.1 (Finset.nonempty_iff_ne_empty.mpr h.2).choose_spec).some.edgeSet',
      F \ (exists_closingPath h.1 (Finset.nonempty_iff_ne_empty.mpr h.2).choose_spec).some.edgeSet')
  else (∅, ∅)

lemma cycleData_spec {F : Finset (Sym2 V)} (hFE : F ⊆ H.edgeFinset)
    (hB : closedEdges H.edgeFinset F ≠ ∅) :
    ∃ (e : Sym2 V) (he : e ∈ closedEdges H.edgeFinset F) (cp : ClosingPath H F e),
      cycleData H F = (insert e cp.edgeSet', F \ cp.edgeSet') := by
  classical
  refine ⟨_, (Finset.nonempty_iff_ne_empty.mpr hB).choose_spec,
    (exists_closingPath hFE (Finset.nonempty_iff_ne_empty.mpr hB).choose_spec).some, ?_⟩
  unfold cycleData
  rw [dif_pos ⟨hFE, hB⟩]

/-- The closed edge is the largest edge of the cycle. -/
lemma ClosingPath.ord_lt {F : Finset (Sym2 V)} {e : Sym2 V} (cp : ClosingPath H F e)
    {f : Sym2 V} (hf : f ∈ cp.edgeSet') : ord f < ord e :=
  (cp.edges_mem f (List.mem_toFinset.mp hf)).2

lemma eq_of_insert_eq {F₁ F₂ : Finset (Sym2 V)} {e₁ e₂ : Sym2 V} (cp₁ : ClosingPath H F₁ e₁)
    (cp₂ : ClosingPath H F₂ e₂) (h : insert e₁ cp₁.edgeSet' = insert e₂ cp₂.edgeSet') :
    e₁ = e₂ ∧ cp₁.edgeSet' = cp₂.edgeSet' := by
  have he : e₁ = e₂ := by
    by_contra hne
    have h1 : e₁ ∈ insert e₂ cp₂.edgeSet' := h ▸ Finset.mem_insert_self _ _
    have h2 : e₂ ∈ insert e₁ cp₁.edgeSet' := h.symm ▸ Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp h1 with h1 | h1
    · exact hne h1
    rcases Finset.mem_insert.mp h2 with h2 | h2
    · exact hne h2.symm
    exact lt_asymm (cp₂.ord_lt h1) (cp₁.ord_lt h2)
  subst he
  refine ⟨rfl, ?_⟩
  have := congrArg (fun S ↦ S.erase e₁) h
  simp only [Finset.erase_insert cp₁.e_notMem_edgeSet', Finset.erase_insert cp₂.e_notMem_edgeSet']
    at this
  exact this

/-- **(4.29)**. -/
theorem sum_intervalInt_le (U : Graphon Ω μ) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hdeg : ∀ x, degree U x ≤ Δ) :
    ∑ F ∈ (forests H.edgeFinset).filter
        (fun F ↦ closedEdges H.edgeFinset F ≠ ∅ ∧ H.girth ≤ F.card),
      intervalInt H.edgeFinset U F ≤
    ∑ s ∈ Finset.range (Fintype.card V + 1), ((cycleSets H s).card : ℝ) *
      ((1 + Δ) ^ H.edgeFinset.card - if s = H.girth then 1 else 0) * Qs U s := by
  classical
  set T := (forests H.edgeFinset).filter
    (fun F ↦ closedEdges H.edgeFinset F ≠ ∅ ∧ H.girth ≤ F.card) with hT
  set E := H.edgeFinset
  set allCyc := (Finset.range (Fintype.card V + 1)).biUnion (cycleSets H) with hallCyc
  set Z := (allCyc ×ˢ E.powerset).filter fun p ↦ p.1.card = H.girth → p.2.Nonempty with hZ
  set f : Finset (Sym2 V) × Finset (Sym2 V) → ℝ := fun p ↦ Δ ^ p.2.card * Qs U p.1.card with hf
  have hf0 : ∀ p, 0 ≤ f p := fun p ↦ mul_nonneg (pow_nonneg hΔ0 _) (Qs_nonneg U _)
  -- each term is bounded by its data
  have hTmem : ∀ F ∈ T, F ⊆ E ∧ IsForest F ∧ closedEdges E F ≠ ∅ ∧ H.girth ≤ F.card := by
    intro F hF
    obtain ⟨hFf, hB, hg⟩ := Finset.mem_filter.mp hF
    exact ⟨(mem_forests.mp hFf).1, (mem_forests.mp hFf).2, hB, hg⟩
  have hbound : ∀ F ∈ T, intervalInt E U F ≤ f (cycleData H F) := by
    intro F hF
    obtain ⟨hFE, hfor, hB, -⟩ := hTmem F hF
    obtain ⟨e, he, cp, hcd⟩ := cycleData_spec hFE hB
    rw [hcd, hf]
    simp only []
    rw [Finset.card_insert_of_notMem cp.e_notMem_edgeSet']
    exact intervalInt_le_closing U hΔ0 hdeg hFE hfor he cp
  -- the data are injective
  have hinj : Set.InjOn (cycleData H) (T : Set (Finset (Sym2 V))) := by
    intro F₁ h₁ F₂ h₂ h
    obtain ⟨hFE₁, -, hB₁, -⟩ := hTmem F₁ h₁
    obtain ⟨hFE₂, -, hB₂, -⟩ := hTmem F₂ h₂
    obtain ⟨e₁, -, cp₁, hcd₁⟩ := cycleData_spec hFE₁ hB₁
    obtain ⟨e₂, -, cp₂, hcd₂⟩ := cycleData_spec hFE₂ hB₂
    rw [hcd₁, hcd₂, Prod.mk.injEq] at h
    obtain ⟨-, hP⟩ := eq_of_insert_eq cp₁ cp₂ h.1
    have h1 := Finset.union_sdiff_of_subset cp₁.edgeSet'_subset
    have h2 := Finset.union_sdiff_of_subset cp₂.edgeSet'_subset
    rw [← h1, ← h2, h.2, hP]
  -- the data lie in `Z`
  have hmaps : ∀ F ∈ T, cycleData H F ∈ Z := by
    intro F hF
    obtain ⟨hFE, -, hB, hg⟩ := hTmem F hF
    obtain ⟨e, he, cp, hcd⟩ := cycleData_spec hFE hB
    have heE := (mem_closedEdges.mp he).1
    have hC := cp.insert_mem_cycleSets heE
    rw [hcd, hZ, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
    refine ⟨⟨?_, Finset.sdiff_subset.trans hFE⟩, fun hcard ↦ ?_⟩
    · rw [hallCyc, Finset.mem_biUnion]
      refine ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le (card_le_of_mem_cycleSets hC)), ?_⟩
      convert hC using 2
      exact Finset.card_insert_of_notMem cp.e_notMem_edgeSet'
    · rw [Finset.card_insert_of_notMem cp.e_notMem_edgeSet'] at hcard
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      have := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hempty)
      omega
  calc ∑ F ∈ T, intervalInt E U F ≤ ∑ F ∈ T, f (cycleData H F) := Finset.sum_le_sum hbound
    _ = ∑ p ∈ T.image (cycleData H), f p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ Z, f p := Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp ↦ by
            obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hp
            exact hmaps F hF) fun p _ _ ↦ hf0 p
    _ = ∑ C ∈ allCyc, ∑ R ∈ E.powerset,
          if C.card = H.girth → R.Nonempty then Δ ^ R.card * Qs U C.card else 0 := by
        rw [hZ, Finset.sum_filter, Finset.sum_product]
    _ = ∑ s ∈ Finset.range (Fintype.card V + 1), ∑ C ∈ cycleSets H s,
          ((1 + Δ) ^ E.card - if s = H.girth then 1 else 0) * Qs U s := by
        rw [hallCyc, Finset.sum_biUnion]
        · refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun C hC ↦ ?_
          have hCs : C.card = s := (mem_cycleSets.mp hC).2.1
          rw [hCs]
          have hite : ∀ R : Finset (Sym2 V),
              (if s = H.girth → R.Nonempty then Δ ^ R.card * Qs U s else 0) =
                (if s = H.girth → R.Nonempty then Δ ^ R.card else 0) * Qs U s := fun R ↦ by
            split_ifs <;> simp
          simp_rw [hite]
          rw [← Finset.sum_mul]
          congr 1
          rw [← Finset.sum_filter]
          by_cases hsg : s = H.girth
          · have hfil : (E.powerset.filter fun R : Finset (Sym2 V) ↦ s = H.girth → R.Nonempty) =
                E.powerset.filter fun R ↦ R.Nonempty := by
              congr 1; funext R; simp [hsg]
            rw [hfil, if_pos hsg]
            have hsplit := Finset.sum_filter_add_sum_filter_not E.powerset
              (fun R : Finset (Sym2 V) ↦ R.Nonempty) (fun R ↦ Δ ^ R.card)
            have hnot : (E.powerset.filter fun R : Finset (Sym2 V) ↦ ¬ R.Nonempty) = {∅} := by
              ext R
              simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
                Finset.mem_singleton]
              constructor
              · rintro ⟨-, h⟩; exact h
              · rintro rfl; exact ⟨Finset.empty_subset _, rfl⟩
            rw [hnot, Finset.sum_singleton, Finset.card_empty, pow_zero, sum_powerset_pow] at hsplit
            linarith
          · rw [Finset.filter_true_of_mem fun R _ h ↦ absurd h hsg, if_neg hsg, sub_zero]
            exact sum_powerset_pow E Δ
        · intro s₁ _ s₂ _ hne
          refine Finset.disjoint_left.mpr fun C h₁ h₂ ↦ hne ?_
          rw [← (mem_cycleSets.mp h₁).2.1, (mem_cycleSets.mp h₂).2.1]
    _ = _ := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end Taeyoung.Paper.Eventual
