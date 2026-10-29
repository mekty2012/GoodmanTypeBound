import Taeyoung.Paper.Profile.Gluing

/-!
# The reference law of the unequal-bag gluing

`G = (κ_H / t(H)) ∏_i T_i` on the padded vertex set, where `T_i = κ_{C'_i}/m_i(C_i)`
is the conditional law, under `ρ_k`, of the padding of bag `i` given the
coordinates of `C_i`.  Integrating out the paddings one bag at a time leaves
`κ_H / t(H)`, so `G` is a probability density (`lintegral_refENN`).
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Taeyoung.Paper.Profile

open Taeyoung Taeyoung.Methods.PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
  {m : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : MaximalCliqueTreeDecomp H m) (k : ℕ)
variable {δ : ℝ}

/-- The padding of bag `i`, inside the padded vertex set. -/
def padSet (i : Fin m) : Finset (ExtV D k) := (∅ : Finset V).disjSum (padOf D k i)

lemma extBag_sdiff_liftBag (i : Fin m) : extBag D k i \ liftBag D k i = padSet D k i := by
  ext x
  rcases x with v | e <;> simp [extBag, liftBag, padSet]

lemma disjoint_extBag_padSet {i j : Fin m} (hij : i ≠ j) :
    Disjoint (extBag D k i) (padSet D k j) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rcases x with v | e
  · simp [padSet] at hx'
  · simp only [inr_mem_extBag] at hx
    simp only [padSet, Finset.inr_mem_disjSum, mem_padOf] at hx'
    exact hij (hx.symm.trans hx')

/-- `T_i = κ_{C'_i} / m_i(C_i)`. -/
noncomputable def padTrans (W : Graphon Ω μ) (i : Fin m) : (ExtV D k → Ω) → ℝ≥0∞ :=
  fun x ↦ (margOn W (extBag D k i) (liftBag D k i) x)⁻¹ * cliqueWeightOnENN (extBag D k i) W x

lemma measurable_padTrans (W : Graphon Ω μ) (i : Fin m) : Measurable (padTrans D k W i) :=
  (measurable_margOn W _ _).inv.mul (measurable_cliqueWeightOnENN _ W)

lemma padTrans_dependsOn (W : Graphon Ω μ) (i : Fin m) :
    FinsetDependsOn (extBag D k i) (padTrans D k W i) :=
  ((margOn_dependsOn W (liftBag_subset D k i)).mono (liftBag_subset D k i)).inv.mul
    fun _ _ hxy ↦ cliqueWeightOnENN_congr_on _ W hxy

lemma lmarginal_padTrans (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (i : Fin m) : lmarginal (fun _ : ExtV D k ↦ μ) (padSet D k i) (padTrans D k W i) =
      fun _ ↦ 1 := by
  have hm : margOn W (extBag D k i) (liftBag D k i) =
      lmarginal (fun _ : ExtV D k ↦ μ) (padSet D k i) (cliqueWeightOnENN (extBag D k i) W) := by
    rw [margOn, extBag_sdiff_liftBag]
  have h := lmarginal_inv_marginal_mul_eq_one (μ := μ) (padSet D k i)
    (measurable_cliqueWeightOnENN (extBag D k i) W)
    (fun x ↦ by
      rw [← hm]
      exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (pow_pos hδpos _))
        (margOn_lower_bound W hδpos.le hδ _ _ x)))
    (fun x ↦ by rw [← hm]; exact margOn_ne_top W _ _ x)
  rw [← hm] at h
  exact h

/-- The paddings, taken together, carry conditional mass one. -/
lemma lmarginal_prod_padTrans (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (S : Finset (Fin m)) :
    lmarginal (fun _ : ExtV D k ↦ μ) (S.biUnion (padSet D k))
        (fun x ↦ ∏ i ∈ S, padTrans D k W i x) = fun _ ↦ 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hdisj : Disjoint (padSet D k a) (S.biUnion (padSet D k)) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        have haj : a ≠ j := by rintro rfl; exact ha hj
        rw [Finset.disjoint_left]
        intro x hx hx'
        rcases x with v | e
        · simp [padSet] at hx
        · simp only [padSet, Finset.inr_mem_disjSum, mem_padOf] at hx hx'
          exact haj (hx.symm.trans hx')
      have hinv : UpdateInvariant (S.biUnion (padSet D k)) (padTrans D k W a) := by
        apply (padTrans_dependsOn D k W a).updateInvariant_of_disjoint
        rw [Finset.disjoint_biUnion_left]
        intro j hj
        exact (disjoint_extBag_padSet D k (by rintro rfl; exact ha hj)).symm
      have hRm : Measurable fun x ↦ ∏ i ∈ S, padTrans D k W i x :=
        Finset.measurable_prod _ fun i _ ↦ measurable_padTrans D k W i
      simp_rw [Finset.prod_insert ha]
      rw [Finset.biUnion_insert, lmarginal_union _ _
        ((measurable_padTrans D k W a).mul hRm) hdisj,
        lmarginal_mul_of_left_updateInvariant _ (measurable_padTrans D k W a) hRm hinv, ih]
      simp only [mul_one]
      exact lmarginal_padTrans D k W hδpos hδ a

/-- The original coordinates. -/
def origSet : Finset (ExtV D k) := (univ : Finset V).disjSum ∅

lemma biUnion_padSet : (univ : Finset (Fin m)).biUnion (padSet D k) = univ \ origSet D k := by
  ext x
  rcases x with v | e
  · simp [padSet, origSet]
  · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, padSet, Finset.inr_mem_disjSum,
      mem_padOf, Finset.mem_sdiff, origSet]
    exact ⟨fun _ ↦ by simp, fun _ ↦ ⟨e.1, rfl⟩⟩

/-- **The reference law** `G = (κ_H / t(H)) ∏_i T_i`. -/
noncomputable def refENN (W : Graphon Ω μ) : (ExtV D k → Ω) → ℝ≥0∞ := fun x ↦
  (ENNReal.ofReal (homDensity H W))⁻¹ *
    ENNReal.ofReal (graphWeight H W fun v ↦ x (Sum.inl v)) * ∏ i, padTrans D k W i x

lemma measurable_origWeight (W : Graphon Ω μ) :
    Measurable fun x : ExtV D k → Ω ↦ ENNReal.ofReal (graphWeight H W fun v ↦ x (Sum.inl v)) :=
  ((measurable_graphWeight H W).comp
    (measurable_pi_lambda _ fun v ↦ measurable_pi_apply (Sum.inl v))).ennreal_ofReal

lemma measurable_refENN (W : Graphon Ω μ) : Measurable (refENN D k W) :=
  (measurable_const.mul (measurable_origWeight D k W)).mul
    (Finset.measurable_prod _ fun i _ ↦ measurable_padTrans D k W i)

/-- Integrating a function of the original coordinates over the padded space. -/
lemma lintegral_comp_inl (F : (V → Ω) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (fun v ↦ x (Sum.inl v)) ∂Measure.pi (fun _ : ExtV D k ↦ μ) =
      ∫⁻ y, F y ∂Measure.pi (fun _ : V ↦ μ) := by
  have hmp := measurePreserving_sumPiEquivProdPi (fun _ : ExtV D k ↦ μ)
  have h := hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
    (fun p : (V → Ω) × (Pad D k → Ω) ↦ F p.1)
  have hcomp : ∀ x : ExtV D k → Ω,
      (fun p : (V → Ω) × (Pad D k → Ω) ↦ F p.1)
        ((MeasurableEquiv.sumPiEquivProdPi fun _ : ExtV D k ↦ Ω) x) =
      F (fun v ↦ x (Sum.inl v)) := fun x ↦ rfl
  simp only [hcomp] at h
  rw [h, lintegral_prod (fun p : (V → Ω) × (Pad D k → Ω) ↦ F p.1)
    (hF.comp measurable_fst).aemeasurable]
  simp

/-- **`G` is a probability density.** -/
theorem lintegral_refENN (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) :
    ∫⁻ x, refENN D k W x ∂Measure.pi (fun _ : ExtV D k ↦ μ) = 1 := by
  classical
  haveI := nonempty_of_isProbabilityMeasure μ
  obtain ⟨ω⟩ := this
  let x₀ : ExtV D k → Ω := fun _ ↦ ω
  set P := univ \ origSet D k with hP
  let cK : (ExtV D k → Ω) → ℝ≥0∞ := fun x ↦ (ENNReal.ofReal (homDensity H W))⁻¹ *
    ENNReal.ofReal (graphWeight H W fun v ↦ x (Sum.inl v))
  have hcKm : Measurable cK := measurable_const.mul (measurable_origWeight D k W)
  have hcKdep : FinsetDependsOn (origSet D k) cK := fun x y hxy ↦ by
    simp only [cK]
    congr 3
    funext v
    exact hxy (Sum.inl v) (by simp [origSet])
  have hcKinv : UpdateInvariant P cK :=
    hcKdep.updateInvariant_of_disjoint Finset.sdiff_disjoint
  have hRm : Measurable fun x ↦ ∏ i, padTrans D k W i x :=
    Finset.measurable_prod _ fun i _ ↦ measurable_padTrans D k W i
  have hmargP : lmarginal (fun _ : ExtV D k ↦ μ) P (refENN D k W) = cK := by
    have := lmarginal_mul_of_left_updateInvariant (μ := μ) P hcKm hRm hcKinv
    have hprod := lmarginal_prod_padTrans D k W hδpos hδ univ
    rw [biUnion_padSet, ← hP] at hprod
    change lmarginal (fun _ : ExtV D k ↦ μ) P (fun x ↦ cK x * ∏ i, padTrans D k W i x) = cK
    rw [this, hprod]
    funext x; simp
  have hmargP' : lmarginal (fun _ : ExtV D k ↦ μ) P cK = cK :=
    hcKdep.lmarginal_eq_self_of_disjoint Finset.sdiff_disjoint
  have hunion : (univ \ P) ∪ P = (univ : Finset (ExtV D k)) := by ext x; simp
  have hdisj : Disjoint (univ \ P) P := Finset.sdiff_disjoint
  have h1 : ∫⁻ x, refENN D k W x ∂Measure.pi (fun _ : ExtV D k ↦ μ) =
      ∫⁻ x, cK x ∂Measure.pi (fun _ : ExtV D k ↦ μ) := by
    rw [lintegral_eq_lmarginal_univ x₀, lintegral_eq_lmarginal_univ x₀, ← hunion,
      lmarginal_union _ _ (measurable_refENN D k W) hdisj,
      lmarginal_union _ _ hcKm hdisj, hmargP, hmargP']
  rw [h1]
  simp only [cK]
  rw [lintegral_const_mul _ (measurable_origWeight D k W),
    lintegral_comp_inl D k (fun y ↦ ENNReal.ofReal (graphWeight H W y))
      (measurable_graphWeight H W).ennreal_ofReal]
  change (ENNReal.ofReal (homDensity H W))⁻¹ *
    ∫⁻ y, ENNReal.ofReal (graphWeight H W y) ∂assignmentMeasure V μ = 1
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_graphWeight H W)
      (ae_of_all _ fun y ↦ graphWeight_nonneg H W y)]
  change (ENNReal.ofReal (homDensity H W))⁻¹ * ENNReal.ofReal (homDensity H W) = 1
  exact ENNReal.inv_mul_cancel
    (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact homDensity_pos_of_lower_bound H W hδpos hδ)
    ENNReal.ofReal_ne_top

end Taeyoung.Paper.Profile
