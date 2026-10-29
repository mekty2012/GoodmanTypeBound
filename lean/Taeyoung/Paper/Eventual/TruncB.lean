import Taeyoung.Paper.Eventual.TruncA
import Taeyoung.Paper.Eventual.Star

/-!
# The exceptional set (`paper.pdf`, proof of Proposition 4.15)

Let `U` be a graphon, `δ ≥ 0`, and `A = {x : d_U(x) > δ}` with `s = μ(A)`,
`t = 1 - s`.  Split `U = U₁ + U₂` with `U₁ = U · 1_{x ∈ A ∨ y ∈ A}`.  Then

* `degree_low_le`: the degree function of `U₂` is at most `δ`;
* `Dfun_high_ge`: retaining in `D_H(U₁) = 𝔼 (N-1)_+` only the events where
  exactly one vertex of `H` lies in `A`,
  `D_H(U₁) ≥ c_* t^{n-3} ∫_A g²`, where `g(x) = ∫_{A^c} U(x,y) dy` and
  `c_* = ∑_v (d_H(v) - 1)_+` (in `TruncC.lean`).  Here `g` is not the girth: with the
  paper's `h = g/(1-s)` this is `D_H(U₁) ≥ c_* (1-s)^{n-1} ∫_A h²`;
* `Dfun_high_ge_mean`: if `s ≤ δ/2` and `(n-3)s ≤ 1/2` then
  `D_H(U₁) ≥ (c_* δ / 16) q₁`, `q₁ = ∫ U₁` (in `TruncD.lean`; it uses (4.35) and
  (4.36) with `g` in place of `h`).
-/

open MeasureTheory Finset SimpleGraph

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

section Split

variable (U : Graphon Ω μ) (δ : ℝ)

/-- The exceptional set `A = {x : d_U(x) > δ}`. -/
def excSet : Set Ω := {x | δ < degree U x}

lemma measurableSet_excSet : MeasurableSet (excSet U δ) :=
  measurableSet_lt measurable_const (measurable_degree U)

/-- The indicator of a measurable set, as a vertex weight. -/
noncomputable def indBdd {S : Set Ω} (hS : MeasurableSet S) : BddFun Ω :=
  BddFun.ofBound (S.indicator 1) (measurable_one.indicator hS) 1 fun x ↦ by
    by_cases hx : x ∈ S <;> simp [hx]

lemma indBdd_apply {S : Set Ω} (hS : MeasurableSet S) (x : Ω) :
    indBdd hS x = S.indicator 1 x := rfl

lemma indBdd_nonneg {S : Set Ω} (hS : MeasurableSet S) (x : Ω) : 0 ≤ indBdd hS x := by
  rw [indBdd_apply]; by_cases hx : x ∈ S <;> simp [hx]

lemma indBdd_le_one {S : Set Ω} (hS : MeasurableSet S) (x : Ω) : indBdd hS x ≤ 1 := by
  rw [indBdd_apply]; by_cases hx : x ∈ S <;> simp [hx]

open scoped Classical in
/-- `U₁ = U · 1_{x ∈ A ∨ y ∈ A}`. -/
noncomputable def highPart : Graphon Ω μ where
  toFun x y := if x ∈ excSet U δ ∨ y ∈ excSet U δ then U x y else 0
  measurable := by
    refine Measurable.ite ?_ U.measurable measurable_const
    exact ((measurableSet_excSet U δ).preimage measurable_fst).union
      ((measurableSet_excSet U δ).preimage measurable_snd)
  nonneg x y := by split_ifs <;> simp [U.nonneg]
  le_one x y := by split_ifs <;> simp [U.le_one]
  symm x y := by
    by_cases h : x ∈ excSet U δ ∨ y ∈ excSet U δ
    · rw [if_pos h, if_pos (Or.symm h), U.symm]
    · rw [if_neg h, if_neg (fun h' ↦ h (Or.symm h'))]

open scoped Classical in
/-- `U₂ = U - U₁ = U · 1_{x ∉ A ∧ y ∉ A}`. -/
noncomputable def lowPart : Graphon Ω μ where
  toFun x y := if x ∈ excSet U δ ∨ y ∈ excSet U δ then 0 else U x y
  measurable := by
    refine Measurable.ite ?_ measurable_const U.measurable
    exact ((measurableSet_excSet U δ).preimage measurable_fst).union
      ((measurableSet_excSet U δ).preimage measurable_snd)
  nonneg x y := by split_ifs <;> simp [U.nonneg]
  le_one x y := by split_ifs <;> simp [U.le_one]
  symm x y := by
    by_cases h : x ∈ excSet U δ ∨ y ∈ excSet U δ
    · rw [if_pos h, if_pos (Or.symm h)]
    · rw [if_neg h, if_neg (fun h' ↦ h (Or.symm h')), U.symm]

lemma high_add_low (x y : Ω) : U x y = highPart U δ x y + lowPart U δ x y := by
  classical
  show U x y = (if _ then U x y else 0) + (if _ then 0 else U x y)
  split_ifs <;> simp

/-- The degree function of `U₂` is at most `δ`. -/
lemma degree_low_le (hδ : 0 ≤ δ) (x : Ω) : degree (lowPart U δ) x ≤ δ := by
  classical
  by_cases hx : x ∈ excSet U δ
  · have : ∀ y, lowPart U δ x y = 0 := fun y ↦ if_pos (Or.inl hx)
    simp only [degree, this, integral_zero]; exact hδ
  · have hle : degree (lowPart U δ) x ≤ degree U x := by
      unfold degree
      refine integral_mono (isBdd_row _ x).integrable (isBdd_row U x).integrable fun y ↦ ?_
      show (if _ then 0 else U x y) ≤ U x y
      split_ifs <;> simp [U.nonneg]
    have : degree U x ≤ δ := not_lt.mp hx
    linarith

lemma meanDeg_high_add_low : meanDeg (highPart U δ) + meanDeg (lowPart U δ) = meanDeg U := by
  unfold meanDeg
  rw [← integral_add (isBdd_degree _).integrable (isBdd_degree _).integrable]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [degree]
  rw [← integral_add (isBdd_row _ x).integrable (isBdd_row _ x).integrable]
  exact integral_congr_ae (ae_of_all _ fun y ↦ (high_add_low U δ x y).symm)

end Split

/-! ### The quantities `s`, `t`, `g` -/

section Quantities

variable (U : Graphon Ω μ) (δ : ℝ)

/-- `1_A`. -/
noncomputable abbrev indA : BddFun Ω := indBdd (measurableSet_excSet U δ)
/-- `1_{A^c}`. -/
noncomputable abbrev indAc : BddFun Ω := indBdd (measurableSet_excSet U δ).compl

/-- `s = μ(A)`. -/
noncomputable def sA : ℝ := ∫ x, indA U δ x ∂μ
/-- `t = μ(A^c)`. -/
noncomputable def tA : ℝ := ∫ x, indAc U δ x ∂μ
/-- `g(x) = ∫_{A^c} U(x,y) dy`. -/
noncomputable def gA (x : Ω) : ℝ := kernelApply U (indAc U δ) x

lemma indA_add_indAc (x : Ω) : indA U δ x + indAc U δ x = 1 := by
  simp only [indA, indAc, indBdd_apply]
  by_cases hx : x ∈ excSet U δ <;> simp [hx]

lemma sA_add_tA : sA U δ + tA U δ = 1 := by
  unfold sA tA
  rw [← integral_add (indA U δ).integrable (indAc U δ).integrable]
  simp [indA_add_indAc]

lemma sA_nonneg : 0 ≤ sA U δ := integral_nonneg fun x ↦ indBdd_nonneg _ x
lemma tA_nonneg : 0 ≤ tA U δ := integral_nonneg fun x ↦ indBdd_nonneg _ x

lemma gA_nonneg (x : Ω) : 0 ≤ gA U δ x :=
  integral_nonneg fun y ↦ mul_nonneg (U.nonneg _ _) (indBdd_nonneg _ y)

lemma gA_le_tA (x : Ω) : gA U δ x ≤ tA U δ := by
  unfold gA kernelApply tA
  refine integral_mono (integrable_kernel_mul U _ x) (indAc U δ).integrable fun y ↦ ?_
  have := indBdd_nonneg (measurableSet_excSet U δ).compl y
  calc U x y * indAc U δ y ≤ 1 * indAc U δ y := mul_le_mul_of_nonneg_right (U.le_one _ _) this
    _ = indAc U δ y := one_mul _

lemma isBdd_gA : IsBdd (gA U δ) := isBdd_kernelApply U (IsBdd.of_bddFun _)

/-- `(1 - U) 1_{A^c} = t - g`. -/
lemma kernelApply_compl_indAc (x : Ω) :
    kernelApply U.compl (indAc U δ) x = tA U δ - gA U δ x := by
  show ∫ z, (1 - U x z) * indAc U δ z ∂μ =
    (∫ z, indAc U δ z ∂μ) - ∫ z, U x z * indAc U δ z ∂μ
  rw [← integral_sub (indAc U δ).integrable (integrable_kernel_mul U _ x)]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []; ring

/-- On `A`, `d_U ≤ s + g`. -/
lemma degree_le_sA_add_gA (x : Ω) : degree U x ≤ sA U δ + gA U δ x := by
  have hsplit : degree U x = (∫ y, U x y * indA U δ y ∂μ) + gA U δ x := by
    unfold degree gA kernelApply
    rw [← integral_add (integrable_kernel_mul U _ x) (integrable_kernel_mul U _ x)]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    simp only []
    rw [← mul_add, indA_add_indAc, mul_one]
  have hle : ∫ y, U x y * indA U δ y ∂μ ≤ sA U δ := by
    unfold sA
    refine integral_mono (integrable_kernel_mul U _ x) (indA U δ).integrable fun y ↦ ?_
    have := indBdd_nonneg (measurableSet_excSet U δ) y
    calc U x y * indA U δ y ≤ 1 * indA U δ y := mul_le_mul_of_nonneg_right (U.le_one _ _) this
      _ = indA U δ y := one_mul _
  linarith

/-- **Markov**: `δ s ≤ ∫ U`. -/
lemma mul_sA_le (hδ : 0 ≤ δ) : δ * sA U δ ≤ meanDeg U := by
  unfold sA meanDeg
  rw [← integral_const_mul]
  refine integral_mono ((indA U δ).integrable.const_mul _) (isBdd_degree U).integrable fun x ↦ ?_
  simp only [indA, indBdd_apply]
  by_cases hx : x ∈ excSet U δ
  · simp only [hx, Set.indicator_of_mem, Pi.one_apply, mul_one]; exact le_of_lt hx
  · simp only [hx, not_false_eq_true, Set.indicator_of_notMem, mul_zero]
    exact degree_nonneg U x

/-- `∫ U₁ ≤ 2 ∫_A d_U`. -/
lemma meanDeg_high_le : meanDeg (highPart U δ) ≤ 2 * ∫ x, indA U δ x * degree U x ∂μ := by
  classical
  have hpt : ∀ x y, highPart U δ x y ≤ U x y * indA U δ x + U x y * indA U δ y := by
    intro x y
    show (if _ then U x y else 0) ≤ _
    simp only [indA, indBdd_apply]
    by_cases hx : x ∈ excSet U δ <;> by_cases hy : y ∈ excSet U δ <;>
      simp [hx, hy, U.nonneg]
  have h1 : meanDeg (highPart U δ) ≤ ∫ x, ∫ y, (U x y * indA U δ x + U x y * indA U δ y) ∂μ ∂μ :=
    dint_mono (Bdd2.graphon _) (((Bdd2.graphon U).mul (Bdd2.left (IsBdd.of_bddFun _))).add
      ((Bdd2.graphon U).mul (Bdd2.right (IsBdd.of_bddFun _)))) hpt
  have h2 : ∫ x, ∫ y, (U x y * indA U δ x + U x y * indA U δ y) ∂μ ∂μ =
      2 * ∫ x, indA U δ x * degree U x ∂μ := by
    have hA := dint_add (μ := μ) ((Bdd2.graphon U).mul (Bdd2.left (IsBdd.of_bddFun (indA U δ))))
      ((Bdd2.graphon U).mul (Bdd2.right (IsBdd.of_bddFun (indA U δ))))
    unfold dint at hA
    rw [hA]
    have e1 : ∫ x, ∫ y, U x y * indA U δ x ∂μ ∂μ = ∫ x, indA U δ x * degree U x ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp only [degree]
      rw [integral_mul_const, mul_comm]
    have e2 : ∫ x, ∫ y, U x y * indA U δ y ∂μ ∂μ = ∫ x, indA U δ x * degree U x ∂μ := by
      have := integral_kernelApply U (IsBdd.of_bddFun (indA U δ))
      unfold kernelApply at this
      rw [this]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp only []; ring
    rw [e1, e2]; ring
  linarith

end Quantities

/-! ### The events "exactly one vertex in `A`" -/

section Events

variable (U : Graphon Ω μ) (δ : ℝ)

/-- The weights `1_A` at `v` and `1_{A^c}` elsewhere. -/
noncomputable def evWeight (v : V) : V → BddFun Ω :=
  Function.update (fun _ ↦ indAc U δ) v (indA U δ)

lemma evWeight_self (v : V) : evWeight U δ v v = indA U δ := Function.update_self _ _ _
lemma evWeight_ne {v u : V} (h : u ≠ v) : evWeight U δ v u = indAc U δ :=
  Function.update_of_ne h _ _

lemma evWeight_nonneg (v u : V) (y : Ω) : 0 ≤ evWeight U δ v u y := by
  by_cases h : u = v
  · subst h; rw [evWeight_self]; exact indBdd_nonneg _ _
  · rw [evWeight_ne U δ h]; exact indBdd_nonneg _ _

lemma evWeight_le_one (v u : V) (y : Ω) : evWeight U δ v u y ≤ 1 := by
  by_cases h : u = v
  · subst h; rw [evWeight_self]; exact indBdd_le_one _ _
  · rw [evWeight_ne U δ h]; exact indBdd_le_one _ _

lemma vertexProd_evWeight_nonneg (v : V) (x : V → Ω) : 0 ≤ vertexProd (evWeight U δ v) x :=
  Finset.prod_nonneg fun u _ ↦ evWeight_nonneg U δ v u _

/-- At most one of the events occurs. -/
lemma sum_vertexProd_evWeight_le (x : V → Ω) :
    ∑ v, vertexProd (evWeight U δ v) x ≤ 1 := by
  classical
  by_cases h : ∃ v, x v ∈ excSet U δ ∧ ∀ u, u ≠ v → x u ∉ excSet U δ
  · obtain ⟨v, hv, hu⟩ := h
    rw [← Finset.add_sum_erase _ _ (mem_univ v)]
    have h1 : vertexProd (evWeight U δ v) x ≤ 1 :=
      Finset.prod_le_one (fun u _ ↦ evWeight_nonneg U δ v u _) fun u _ ↦
        evWeight_le_one U δ v u _
    have h2 : ∑ w ∈ univ.erase v, vertexProd (evWeight U δ w) x = 0 := by
      refine Finset.sum_eq_zero fun w hw ↦ ?_
      have hwv : w ≠ v := Finset.ne_of_mem_erase hw
      refine Finset.prod_eq_zero (i := w) (mem_univ w) ?_
      rw [evWeight_self, indBdd_apply]
      simp [hu w hwv]
    linarith
  · push_neg at h
    have : ∀ v, vertexProd (evWeight U δ v) x = 0 := by
      intro v
      by_cases hv : x v ∈ excSet U δ
      · obtain ⟨u, huv, hu⟩ := h v hv
        refine Finset.prod_eq_zero (i := u) (mem_univ u) ?_
        rw [evWeight_ne U δ huv, indBdd_apply]
        simp [hu]
      · refine Finset.prod_eq_zero (i := v) (mem_univ v) ?_
        rw [evWeight_self, indBdd_apply]
        simp [hv]
    simp [this]

/-- The edges at `v`. -/
lemma filter_mem_eq_starEdges (v : V) :
    H.edgeFinset.filter (fun e ↦ v ∈ e) = starEdges v (H.neighborFinset v) := by
  ext e
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, mem_starEdges,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨he, hv⟩
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
    exact ⟨w, he, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, Sym2.mem_mk_left v w⟩

/-- `ψ_v = ∏_{e ∋ v} (1 - U_e) - 1 + ∑_{e ∋ v} U_e`. -/
noncomputable def psiV (v : V) (x : V → Ω) : ℝ :=
  ∏ e ∈ starEdges v (H.neighborFinset v), (1 - edgeValue U x e) - 1 +
    ∑ e ∈ starEdges v (H.neighborFinset v), edgeValue U x e

/-- On the event that `v` is the only vertex in `A`, `φ(U₁) = ψ_v(U)`. -/
lemma vertexProd_mul_Dint_eq (v : V) (x : V → Ω) :
    vertexProd (evWeight U δ v) x * Dint H (highPart U δ) x =
      vertexProd (evWeight U δ v) x * psiV (H := H) U v x := by
  classical
  by_cases hE : x v ∈ excSet U δ ∧ ∀ u, u ≠ v → x u ∉ excSet U δ
  · obtain ⟨hv, hu⟩ := hE
    congr 1
    have hval : ∀ e ∈ H.edgeFinset, edgeValue (highPart U δ) x e =
        if v ∈ e then edgeValue U x e else 0 := by
      intro e he
      induction e using Sym2.inductionOn with
      | _ a b =>
        rw [edgeValue_mk, edgeValue_mk]
        show (if x a ∈ excSet U δ ∨ x b ∈ excSet U δ then U (x a) (x b) else 0) = _
        by_cases hve : v ∈ s(a, b)
        · rw [if_pos hve, if_pos]
          rcases Sym2.mem_iff.mp hve with rfl | rfl
          · exact Or.inl hv
          · exact Or.inr hv
        · rw [if_neg hve, if_neg]
          rintro (h | h)
          · exact hu a (fun h' ↦ hve (h' ▸ Sym2.mem_mk_left a b)) h
          · exact hu b (fun h' ↦ hve (h' ▸ Sym2.mem_mk_right a b)) h
    unfold Dint psiV
    rw [Finset.prod_congr rfl fun e he ↦ by rw [hval e he],
      Finset.sum_congr rfl hval, ← filter_mem_eq_starEdges v]
    rw [Finset.prod_filter, Finset.sum_filter]
    congr 2
    · refine Finset.prod_congr rfl fun e _ ↦ ?_
      split_ifs <;> simp
  · have h0 : vertexProd (evWeight U δ v) x = 0 := by
      simp only [not_and_or, not_forall, not_not] at hE
      rcases hE with h | ⟨u, huv, hu⟩
      · refine Finset.prod_eq_zero (i := v) (mem_univ v) ?_
        rw [evWeight_self, indBdd_apply]; simp [h]
      · refine Finset.prod_eq_zero (i := u) (mem_univ u) ?_
        rw [evWeight_ne U δ huv, indBdd_apply]; simp [hu]
    rw [h0, zero_mul, zero_mul]

end Events

end Taeyoung.Paper.Eventual
