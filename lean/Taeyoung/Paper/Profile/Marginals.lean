import Taeyoung.Methods.PureChordal.EntropyGluing

/-!
# Marginals of a clique law, and the per-level Gibbs inequality

Fix a finite vertex type `I`, a finset `B ⊆ I` and the normalized clique law
`ρ_B = κ_B / t_{|B|}` on the coordinates of `B`.  For `A ⊆ B`, its marginal on
`A` is `margOn W B A / t_{|B|}`, where `margOn W B A` integrates `κ_B` over the
coordinates of `B \ A`.  The bracket of (2.5),

```
B_j = ℋ(X_1,…,X_j) + (j choose 2)·E log W(X_1,X_2) = ∫ ρ_j log (κ_j / ρ_j)
```

(`ρ_j` the law of `(X_1,…,X_j)`), is, up to the constant `log t_{|B|}`, the expectation under `ρ_B` of
`phi W B A = log κ_A - log margOn W B A`.  Two facts are needed.

* `integral_nb_mul_phi_le` — **Gibbs**: `E_{ρ_B}[phi W B A] ≤ log t_{|A|} - log t_{|B|}`,
  i.e. `B_j ≤ log t_j`.  It is Gibbs' inequality for the marginal of `ρ_B` on `A`
  against `κ_A / t_{|A|}`.
* `integral_nb_mul_phi_perm` — **exchangeability**: the expectation depends on
  `(A, B)` only through `|A|` and `|B|`, because a permutation of the coordinates
  carrying `B` to `B'` and `A` to `A'` transports one integrand to the other.

Everything is for a graphon bounded below by some `δ > 0` (the regularized
graphons of `Methods/PureChordal/Regularization.lean`), so all logarithms are
bounded.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Taeyoung.Paper.Profile

open Taeyoung Taeyoung.Methods.PureChordal

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The marginal of a clique weight -/

/-- `∫ κ_B` over the coordinates of `B \ A`. -/
noncomputable def margOn (W : Graphon Ω μ) (B A : Finset I) : (I → Ω) → ℝ≥0∞ :=
  lmarginal (fun _ : I ↦ μ) (B \ A) (cliqueWeightOnENN B W)

lemma measurable_margOn (W : Graphon Ω μ) (B A : Finset I) : Measurable (margOn W B A) :=
  (measurable_cliqueWeightOnENN B W).lmarginal _

lemma margOn_dependsOn (W : Graphon Ω μ) {B A : Finset I} (hAB : A ⊆ B) :
    FinsetDependsOn A (margOn W B A) := by
  have hdep : FinsetDependsOn B (cliqueWeightOnENN B W) := fun x y hxy ↦
    cliqueWeightOnENN_congr_on B W hxy
  have h := hdep.lmarginal (μ := μ) (T := B \ A)
  have hset : B \ (B \ A) = A := by
    ext v; simp only [Finset.mem_sdiff, not_and, not_not]
    exact ⟨fun h ↦ h.2 h.1, fun h ↦ ⟨hAB h, fun _ ↦ h⟩⟩
  rw [hset] at h
  exact h

lemma margOn_le_one (W : Graphon Ω μ) (B A : Finset I) (x : I → Ω) : margOn W B A x ≤ 1 := by
  calc margOn W B A x ≤ lmarginal (fun _ : I ↦ μ) (B \ A) (fun _ ↦ 1) x :=
        lmarginal_mono (fun y ↦ cliqueWeightOnENN_le_one B W y) x
    _ = 1 := by unfold lmarginal; simp

lemma margOn_lower_bound (W : Graphon Ω μ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ a b, δ ≤ W a b)
    (B A : Finset I) (x : I → Ω) :
    ENNReal.ofReal (δ ^ (pairsIn B).card) ≤ margOn W B A x := by
  calc ENNReal.ofReal (δ ^ (pairsIn B).card) =
        lmarginal (fun _ : I ↦ μ) (B \ A) (fun _ ↦ ENNReal.ofReal (δ ^ (pairsIn B).card)) x := by
        unfold lmarginal; simp
    _ ≤ margOn W B A x :=
        lmarginal_mono (fun y ↦ cliqueWeightOnENN_lower_bound B W hδ0 hδ y) x

lemma margOn_ne_top (W : Graphon Ω μ) (B A : Finset I) (x : I → Ω) : margOn W B A x ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (margOn_le_one W B A x)

lemma margOn_toReal_pos (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (B A : Finset I) (x : I → Ω) : 0 < (margOn W B A x).toReal := by
  apply ENNReal.toReal_pos _ (margOn_ne_top W B A x)
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (pow_pos hδpos _))
    (margOn_lower_bound W hδpos.le hδ B A x))

lemma margOn_toReal_lower (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (B A : Finset I) (x : I → Ω) : δ ^ (pairsIn B).card ≤ (margOn W B A x).toReal := by
  have h := margOn_lower_bound W hδpos.le hδ B A x
  rw [← ENNReal.ofReal_toReal (margOn_ne_top W B A x)] at h
  exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h

lemma margOn_toReal_le_one (W : Graphon Ω μ) (B A : Finset I) (x : I → Ω) :
    (margOn W B A x).toReal ≤ 1 := by
  have h := margOn_le_one W B A x
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)

/-- Integrating over all of `B` gives the clique density. -/
lemma margOn_empty (W : Graphon Ω μ) (B : Finset I) :
    margOn W B ∅ = fun _ ↦ ENNReal.ofReal (cliqueDensity B.card W) := by
  funext x
  unfold margOn
  rw [Finset.sdiff_empty]
  have h := lmarginal_cliqueWeightOnENN_compl_eq_diff (μ := μ) (S := ∅) (A := B)
    (Finset.empty_subset _) W
  rw [Finset.sdiff_empty, Finset.sdiff_empty] at h
  rw [← h, lmarginal_univ]
  have := lintegral_cliqueWeightOnENN (μ := μ) B W
  simp only [assignmentMeasure] at this
  exact this

/-- Integrating over nothing leaves the weight. -/
lemma margOn_self (W : Graphon Ω μ) (B : Finset I) : margOn W B B = cliqueWeightOnENN B W := by
  unfold margOn
  rw [Finset.sdiff_self, lmarginal_empty]

/-! ### Integrating out the coordinates of `B \ A` -/

/-- Against a test function of the coordinates in `A ⊆ B`, `κ_B` integrates like its
marginal on `A`. -/
theorem lintegral_cliqueWeightOnENN_mul (W : Graphon Ω μ) {B A : Finset I} (hAB : A ⊆ B)
    {F : (I → Ω) → ℝ≥0∞} (hF : Measurable F) (hFdep : FinsetDependsOn A F) :
    ∫⁻ x, cliqueWeightOnENN B W x * F x ∂Measure.pi (fun _ : I ↦ μ) =
      ∫⁻ x, margOn W B A x * F x ∂Measure.pi (fun _ : I ↦ μ) := by
  classical
  haveI := nonempty_of_isProbabilityMeasure μ
  obtain ⟨ω⟩ := this
  let x₀ : I → Ω := fun _ ↦ ω
  set T := B \ A with hT
  have hdisj : Disjoint (Finset.univ \ T) T := Finset.sdiff_disjoint
  have hunion : (Finset.univ \ T) ∪ T = Finset.univ := by
    ext v; simp
  have hFinv : UpdateInvariant T F := hFdep.updateInvariant_of_disjoint Finset.sdiff_disjoint
  have hmF : Measurable fun x ↦ cliqueWeightOnENN B W x * F x :=
    (measurable_cliqueWeightOnENN B W).mul hF
  have hmG : Measurable fun x ↦ margOn W B A x * F x := (measurable_margOn W B A).mul hF
  have h1 : lmarginal (fun _ : I ↦ μ) T (fun x ↦ cliqueWeightOnENN B W x * F x) =
      fun x ↦ margOn W B A x * F x := by
    rw [lmarginal_mul_of_right_updateInvariant T (measurable_cliqueWeightOnENN B W) hF hFinv]
    rfl
  have h2 : lmarginal (fun _ : I ↦ μ) T (fun x ↦ margOn W B A x * F x) =
      fun x ↦ margOn W B A x * F x := by
    have hdep : FinsetDependsOn A fun x ↦ margOn W B A x * F x :=
      (margOn_dependsOn W hAB).mul hFdep
    exact hdep.lmarginal_eq_self_of_disjoint Finset.sdiff_disjoint
  rw [lintegral_eq_lmarginal_univ x₀, lintegral_eq_lmarginal_univ x₀, ← hunion,
    lmarginal_union _ _ hmF hdisj, lmarginal_union _ _ hmG hdisj, h1, h2]

/-! ### The per-level Gibbs inequality -/

/-- `ρ_B = κ_B / t_{|B|}`, as a real function. -/
noncomputable def nb (W : Graphon Ω μ) (B : Finset I) (x : I → Ω) : ℝ :=
  PureCliqueTreeDecomp.cliqueWeightOn B W x / cliqueDensity B.card W

/-- `phi W B A = log κ_A - log margOn W B A`. -/
noncomputable def phi (W : Graphon Ω μ) (B A : Finset I) (x : I → Ω) : ℝ :=
  Real.log (PureCliqueTreeDecomp.cliqueWeightOn A W x) - Real.log (margOn W B A x).toReal

lemma measurable_nb (W : Graphon Ω μ) (B : Finset I) : Measurable (nb W B) :=
  (measurable_cliqueWeightOn B W).div_const _

lemma measurable_phi (W : Graphon Ω μ) (B A : Finset I) : Measurable (phi W B A) :=
  ((measurable_cliqueWeightOn A W).log).sub ((measurable_margOn W B A).ennreal_toReal.log)

variable {δ : ℝ}

lemma cliqueWeightOn_pos (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (A : Finset I) (x : I → Ω) : 0 < PureCliqueTreeDecomp.cliqueWeightOn A W x :=
  lt_of_lt_of_le (pow_pos hδpos _) (cliqueWeightOn_lower_bound A W hδpos.le hδ x)

lemma cliqueDensity_pos' (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) (j : ℕ) :
    0 < cliqueDensity j W :=
  cliqueDensity_pos_of_lower_bound j W hδpos hδ

/-- `phi` is bounded. -/
lemma abs_phi_le (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (B A : Finset I) (x : I → Ω) :
    |phi W B A x| ≤ -Real.log (δ ^ (pairsIn A).card) - Real.log (δ ^ (pairsIn B).card) := by
  have hκ := cliqueWeightOn_pos W hδpos hδ A x
  have hκl := cliqueWeightOn_lower_bound A W hδpos.le hδ x
  have hκu := cliqueWeightOn_le_one A W x
  have hm := margOn_toReal_pos W hδpos hδ B A x
  have hml := margOn_toReal_lower W hδpos hδ B A x
  have hmu := margOn_toReal_le_one W B A x
  have h1 : Real.log (δ ^ (pairsIn A).card) ≤ Real.log (PureCliqueTreeDecomp.cliqueWeightOn A W x) :=
    Real.log_le_log (pow_pos hδpos _) hκl
  have h2 : Real.log (PureCliqueTreeDecomp.cliqueWeightOn A W x) ≤ 0 := Real.log_nonpos hκ.le hκu
  have h3 : Real.log (δ ^ (pairsIn B).card) ≤ Real.log (margOn W B A x).toReal :=
    Real.log_le_log (pow_pos hδpos _) hml
  have h4 : Real.log (margOn W B A x).toReal ≤ 0 := Real.log_nonpos hm.le hmu
  unfold phi
  rw [abs_le]
  constructor <;> linarith

lemma integrable_of_bounded {f : (I → Ω) → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable f (Measure.pi fun _ : I ↦ μ) :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)

/-- Against a nonnegative bounded test function of the coordinates in `A ⊆ B`,
`κ_B` integrates like its marginal on `A` (real form). -/
theorem integral_cliqueWeightOn_mul (W : Graphon Ω μ) {B A : Finset I} (hAB : A ⊆ B)
    {F : (I → Ω) → ℝ} (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x) {C : ℝ} (hFC : ∀ x, F x ≤ C)
    (hFdep : ∀ ⦃x y : I → Ω⦄, (∀ i ∈ A, x i = y i) → F x = F y) :
    ∫ x, PureCliqueTreeDecomp.cliqueWeightOn B W x * F x ∂Measure.pi (fun _ : I ↦ μ) =
      ∫ x, (margOn W B A x).toReal * F x ∂Measure.pi (fun _ : I ↦ μ) := by
  haveI := nonempty_of_isProbabilityMeasure μ
  have hC0 : 0 ≤ C := (hF0 (Classical.arbitrary _)).trans (hFC _)
  have hint1 : Integrable (fun x ↦ PureCliqueTreeDecomp.cliqueWeightOn B W x * F x)
      (Measure.pi fun _ : I ↦ μ) :=
    integrable_of_bounded ((measurable_cliqueWeightOn B W).mul hF) C fun x ↦ by
      rw [abs_of_nonneg (mul_nonneg (cliqueWeightOn_nonneg B W x) (hF0 x))]
      calc _ ≤ 1 * F x := mul_le_mul_of_nonneg_right (cliqueWeightOn_le_one B W x) (hF0 x)
        _ ≤ C := by rw [one_mul]; exact hFC x
  have hint2 : Integrable (fun x ↦ (margOn W B A x).toReal * F x)
      (Measure.pi fun _ : I ↦ μ) :=
    integrable_of_bounded ((measurable_margOn W B A).ennreal_toReal.mul hF) C fun x ↦ by
      rw [abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hF0 x))]
      calc _ ≤ 1 * F x := mul_le_mul_of_nonneg_right (margOn_toReal_le_one W B A x) (hF0 x)
        _ ≤ C := by rw [one_mul]; exact hFC x
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦
      mul_nonneg (cliqueWeightOn_nonneg B W x) (hF0 x)) hint1.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦
      mul_nonneg ENNReal.toReal_nonneg (hF0 x)) hint2.aestronglyMeasurable]
  congr 1
  have hFE : Measurable fun x ↦ ENNReal.ofReal (F x) := hF.ennreal_ofReal
  have hFEdep : FinsetDependsOn A fun x ↦ ENNReal.ofReal (F x) := fun x y hxy ↦ by
    simp only [hFdep hxy]
  have h := lintegral_cliqueWeightOnENN_mul (μ := μ) W hAB hFE hFEdep
  simp only [cliqueWeightOnENN] at h
  have e1 : (fun x ↦ ENNReal.ofReal (PureCliqueTreeDecomp.cliqueWeightOn B W x * F x)) =
      fun x ↦ ENNReal.ofReal (PureCliqueTreeDecomp.cliqueWeightOn B W x) *
        ENNReal.ofReal (F x) := by
    funext x; rw [ENNReal.ofReal_mul (cliqueWeightOn_nonneg B W x)]
  have e2 : (fun x ↦ ENNReal.ofReal ((margOn W B A x).toReal * F x)) =
      fun x ↦ margOn W B A x * ENNReal.ofReal (F x) := by
    funext x
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (margOn_ne_top W B A x)]
  rw [e1, e2]
  exact h

/-- **The per-level Gibbs inequality**: `E_{ρ_B}[log κ_A - log margOn W B A] ≤
log t_{|A|} - log t_{|B|}` for `A ⊆ B`. -/
theorem integral_nb_mul_phi_le (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    {B A : Finset I} (hAB : A ⊆ B) :
    ∫ x, nb W B x * phi W B A x ∂Measure.pi (fun _ : I ↦ μ) ≤
      Real.log (cliqueDensity A.card W) - Real.log (cliqueDensity B.card W) := by
  set tA := cliqueDensity A.card W
  set tB := cliqueDensity B.card W
  have htA : 0 < tA := cliqueDensity_pos' W hδpos hδ _
  have htB : 0 < tB := cliqueDensity_pos' W hδpos hδ _
  -- the comparison density `g = κ_B κ_A / (t_A · margOn)`
  let g : (I → Ω) → ℝ := fun x ↦
    PureCliqueTreeDecomp.cliqueWeightOn B W x *
      (PureCliqueTreeDecomp.cliqueWeightOn A W x / (tA * (margOn W B A x).toReal))
  have hm := fun x ↦ margOn_toReal_pos W hδpos hδ B A x
  have hgmeas : Measurable g := (measurable_cliqueWeightOn B W).mul
    ((measurable_cliqueWeightOn A W).div
      (measurable_const.mul (measurable_margOn W B A).ennreal_toReal))
  have hfmeas : Measurable (nb W B) := measurable_nb W B
  -- bounds
  have hδe : ∀ (e : ℕ), 0 < δ ^ e := fun e ↦ pow_pos hδpos e
  have hf_lower : ∃ a > 0, ∀ x, a ≤ nb W B x :=
    ⟨δ ^ (pairsIn B).card / tB, div_pos (hδe _) htB, fun x ↦
      div_le_div_of_nonneg_right (cliqueWeightOn_lower_bound B W hδpos.le hδ x) htB.le⟩
  have hf_upper : ∃ b > 0, ∀ x, nb W B x ≤ b :=
    ⟨1 / tB, div_pos one_pos htB, fun x ↦
      div_le_div_of_nonneg_right (cliqueWeightOn_le_one B W x) htB.le⟩
  have hg_lower : ∃ a > 0, ∀ x, a ≤ g x := by
    refine ⟨δ ^ (pairsIn B).card * (δ ^ (pairsIn A).card / (tA * 1)),
      mul_pos (hδe _) (div_pos (hδe _) (by linarith)), fun x ↦ ?_⟩
    apply mul_le_mul (cliqueWeightOn_lower_bound B W hδpos.le hδ x) _
      (div_nonneg (hδe _).le (by linarith)) (cliqueWeightOn_nonneg B W x)
    apply div_le_div₀ (cliqueWeightOn_nonneg A W x) (cliqueWeightOn_lower_bound A W hδpos.le hδ x)
      (mul_pos htA (hm x))
    exact mul_le_mul_of_nonneg_left (margOn_toReal_le_one W B A x) htA.le
  have hg_upper : ∃ b > 0, ∀ x, g x ≤ b := by
    refine ⟨1 * (1 / (tA * δ ^ (pairsIn B).card)),
      mul_pos one_pos (one_div_pos.mpr (mul_pos htA (hδe _))), fun x ↦ ?_⟩
    apply mul_le_mul (cliqueWeightOn_le_one B W x) _
      (div_nonneg (cliqueWeightOn_nonneg A W x) (mul_pos htA (hm x)).le) zero_le_one
    apply div_le_div₀ zero_le_one (cliqueWeightOn_le_one A W x)
      (mul_pos htA (hδe _))
    exact mul_le_mul_of_nonneg_left (margOn_toReal_lower W hδpos hδ B A x) htA.le
  obtain ⟨af, haf, hflo⟩ := hf_lower
  obtain ⟨bf, hbf, hfhi⟩ := hf_upper
  obtain ⟨ag, hag, hglo⟩ := hg_lower
  obtain ⟨bg, hbg, hghi⟩ := hg_upper
  have hfint : Integrable (nb W B) (Measure.pi fun _ : I ↦ μ) :=
    integrable_of_bounded hfmeas bf fun x ↦ by
      rw [abs_of_nonneg (haf.le.trans (hflo x))]; exact hfhi x
  have hgint : Integrable g (Measure.pi fun _ : I ↦ μ) :=
    integrable_of_bounded hgmeas bg fun x ↦ by
      rw [abs_of_nonneg (hag.le.trans (hglo x))]; exact hghi x
  -- normalizations
  have hf_one : ∫ x, nb W B x ∂Measure.pi (fun _ : I ↦ μ) = 1 := by
    unfold nb
    rw [integral_div]
    have := integral_cliqueWeightOn (μ := μ) B W
    simp only [assignmentMeasure] at this
    rw [this]
    exact div_self htB.ne'
  have hg_one : ∫ x, g x ∂Measure.pi (fun _ : I ↦ μ) = 1 := by
    have hF0 : ∀ x, 0 ≤ PureCliqueTreeDecomp.cliqueWeightOn A W x /
        (tA * (margOn W B A x).toReal) := fun x ↦
      div_nonneg (cliqueWeightOn_nonneg A W x) (mul_pos htA (hm x)).le
    have hstep := integral_cliqueWeightOn_mul (μ := μ) W hAB
      (F := fun x ↦ PureCliqueTreeDecomp.cliqueWeightOn A W x / (tA * (margOn W B A x).toReal))
      ((measurable_cliqueWeightOn A W).div
        (measurable_const.mul (measurable_margOn W B A).ennreal_toReal))
      hF0 (C := 1 / (tA * δ ^ (pairsIn B).card)) (fun x ↦ by
        apply div_le_div₀ zero_le_one (cliqueWeightOn_le_one A W x) (mul_pos htA (hδe _))
        exact mul_le_mul_of_nonneg_left (margOn_toReal_lower W hδpos hδ B A x) htA.le)
      (fun x y hxy ↦ by
        have h1 := cliqueWeightOn_congr_on A W hxy
        have h2 := margOn_dependsOn (μ := μ) W hAB hxy
        simp only [h1, h2])
    show ∫ x, PureCliqueTreeDecomp.cliqueWeightOn B W x *
        (PureCliqueTreeDecomp.cliqueWeightOn A W x / (tA * (margOn W B A x).toReal))
        ∂Measure.pi (fun _ : I ↦ μ) = 1
    rw [hstep]
    have hsimp : ∀ x, (margOn W B A x).toReal *
        (PureCliqueTreeDecomp.cliqueWeightOn A W x / (tA * (margOn W B A x).toReal)) =
        PureCliqueTreeDecomp.cliqueWeightOn A W x / tA := fun x ↦ by
      have h0 := (hm x).ne'
      rw [mul_div_assoc', mul_comm tA, ← div_div, mul_div_cancel_left₀ _ h0]
    simp_rw [hsimp]
    rw [integral_div]
    have := integral_cliqueWeightOn (μ := μ) A W
    simp only [assignmentMeasure] at this
    rw [this]
    exact div_self htA.ne'
  have hgibbs := integral_mul_log_div_nonpos_of_exists_bounds hfmeas hgmeas hfint hgint
    hf_one hg_one ⟨af, haf, hflo⟩ ⟨ag, hag, hglo⟩ ⟨bf, hbf, hfhi⟩ ⟨bg, hbg, hghi⟩
  -- the logarithm of the ratio
  have hratio : ∀ x, Real.log (g x / nb W B x) =
      phi W B A x + (Real.log tB - Real.log tA) := by
    intro x
    have hκB := cliqueWeightOn_pos W hδpos hδ B x
    have hκA := cliqueWeightOn_pos W hδpos hδ A x
    have : g x / nb W B x = PureCliqueTreeDecomp.cliqueWeightOn A W x * tB /
        (tA * (margOn W B A x).toReal) := by
      simp only [g, nb]
      field_simp
      rfl
    rw [this, Real.log_div (by positivity) (by have := hm x; positivity),
      Real.log_mul hκA.ne' htB.ne', Real.log_mul htA.ne' (hm x).ne']
    unfold phi
    ring
  simp_rw [hratio, mul_add] at hgibbs
  have hint_phi : Integrable (fun x ↦ nb W B x * phi W B A x) (Measure.pi fun _ : I ↦ μ) :=
    integrable_of_bounded (hfmeas.mul (measurable_phi W B A))
      (bf * (-Real.log (δ ^ (pairsIn A).card) - Real.log (δ ^ (pairsIn B).card))) fun x ↦ by
        rw [abs_mul, abs_of_nonneg (haf.le.trans (hflo x))]
        exact mul_le_mul (hfhi x) (abs_phi_le W hδpos hδ B A x) (abs_nonneg _) hbf.le
  rw [integral_add hint_phi (hfint.mul_const _), integral_mul_const, hf_one, one_mul] at hgibbs
  linarith

/-! ### Exchangeability -/

/-- Relabelling the coordinates relabels a clique weight. -/
lemma cliqueWeightOn_comp_perm (W : Graphon Ω μ) (σ : Equiv.Perm I) (B : Finset I)
    (y : I → Ω) :
    PureCliqueTreeDecomp.cliqueWeightOn B W (fun v ↦ y (σ v)) =
      PureCliqueTreeDecomp.cliqueWeightOn (B.map σ.toEmbedding) W y := by
  unfold PureCliqueTreeDecomp.cliqueWeightOn
  have himage : pairsIn (B.map σ.toEmbedding) = (pairsIn B).map
      ⟨Sym2.map σ, Sym2.map.injective σ.injective⟩ := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [mk_mem_pairsIn, Finset.mem_map, Function.Embedding.coeFn_mk,
        Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨huv, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
        refine ⟨s(a, b), mk_mem_pairsIn.mpr ⟨fun h ↦ huv (by rw [h]), ha, hb⟩, by simp⟩
      · rintro ⟨e, he, hee⟩
        induction e using Sym2.inductionOn with
        | _ a b =>
          rw [mk_mem_pairsIn] at he
          rw [Sym2.map_mk, Sym2.eq_iff] at hee
          rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨fun h ↦ he.1 (σ.injective h), ⟨a, he.2.1, rfl⟩, ⟨b, he.2.2, rfl⟩⟩
          · exact ⟨fun h ↦ he.1 (σ.injective h).symm, ⟨b, he.2.2, rfl⟩, ⟨a, he.2.1, rfl⟩⟩
  rw [himage, Finset.prod_map]
  refine Finset.prod_congr rfl fun e _ ↦ ?_
  induction e using Sym2.inductionOn with
  | _ a b => simp [edgeValue]

lemma cliqueWeightOnENN_comp_perm (W : Graphon Ω μ) (σ : Equiv.Perm I) (B : Finset I)
    (y : I → Ω) :
    cliqueWeightOnENN B W (fun v ↦ y (σ v)) = cliqueWeightOnENN (B.map σ.toEmbedding) W y := by
  simp only [cliqueWeightOnENN, cliqueWeightOn_comp_perm]

/-- Relabelling the coordinates relabels the marginal. -/
lemma margOn_comp_perm (W : Graphon Ω μ) (σ : Equiv.Perm I) (B A : Finset I) (y : I → Ω) :
    margOn W B A (fun v ↦ y (σ v)) =
      margOn W (B.map σ.toEmbedding) (A.map σ.toEmbedding) y := by
  classical
  unfold margOn
  have hrename := lmarginal_image (μ := fun _ : I ↦ μ) σ.injective (B \ A)
    (measurable_cliqueWeightOnENN B W) y
  have hrename' :
      lmarginal (fun _ : I ↦ μ) (B \ A) (cliqueWeightOnENN B W) (fun v ↦ y (σ v)) =
        lmarginal (fun _ : I ↦ μ) ((B \ A).image σ)
          (fun z ↦ cliqueWeightOnENN B W (fun v ↦ z (σ v))) y := by
    (convert hrename.symm using 1; rfl)
  have himg : (B \ A).image σ = B.map σ.toEmbedding \ A.map σ.toEmbedding := by
    rw [← Finset.map_sdiff]
    ext v
    simp only [Finset.mem_image, Finset.mem_map, Equiv.coe_toEmbedding]
  have hfun : (fun z : I → Ω ↦ cliqueWeightOnENN B W (fun v ↦ z (σ v))) =
      cliqueWeightOnENN (B.map σ.toEmbedding) W := by
    funext z
    exact cliqueWeightOnENN_comp_perm W σ B z
  rw [hrename', himg, hfun]

/-- `phi` relabels. -/
lemma phi_comp_perm (W : Graphon Ω μ) (σ : Equiv.Perm I) (B A : Finset I) (y : I → Ω) :
    phi W B A (fun v ↦ y (σ v)) = phi W (B.map σ.toEmbedding) (A.map σ.toEmbedding) y := by
  unfold phi
  rw [cliqueWeightOn_comp_perm, margOn_comp_perm]

lemma nb_comp_perm (W : Graphon Ω μ) (σ : Equiv.Perm I) (B : Finset I) (y : I → Ω) :
    nb W B (fun v ↦ y (σ v)) = nb W (B.map σ.toEmbedding) y := by
  unfold nb
  rw [cliqueWeightOn_comp_perm, Finset.card_map]

/-- The product measure is invariant under a permutation of the coordinates. -/
lemma integral_comp_perm (σ : Equiv.Perm I) (F : (I → Ω) → ℝ) :
    ∫ y, F (fun v ↦ y (σ v)) ∂Measure.pi (fun _ : I ↦ μ) =
      ∫ y, F y ∂Measure.pi (fun _ : I ↦ μ) := by
  let q : (I → Ω) ≃ᵐ (I → Ω) := MeasurableEquiv.piCongrLeft (fun _ : I ↦ Ω) σ.symm
  have hq : MeasurePreserving q (Measure.pi fun _ : I ↦ μ) (Measure.pi fun _ : I ↦ μ) :=
    measurePreserving_piCongrLeft (fun _ : I ↦ μ) σ.symm
  rw [← hq.integral_comp' (g := F)]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show F (fun v ↦ y (σ v)) = F (q y)
  congr 1
  funext v
  simp [q, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

/-- A permutation of `I` carrying `B` onto `B'` and `A ⊆ B` onto `A' ⊆ B'`. -/
lemma exists_perm_map {B A B' A' : Finset I} (hAB : A ⊆ B) (hAB' : A' ⊆ B')
    (hB : B.card = B'.card) (hA : A.card = A'.card) :
    ∃ σ : Equiv.Perm I, B.map σ.toEmbedding = B' ∧ A.map σ.toEmbedding = A' := by
  classical
  have e₁ : ↥A ≃ ↥A' := Fintype.equivOfCardEq (by simpa using hA)
  have e₂ : ↥(B \ A) ≃ ↥(B' \ A') := Fintype.equivOfCardEq (by
    simp only [Fintype.card_coe]
    rw [Finset.card_sdiff_of_subset hAB, Finset.card_sdiff_of_subset hAB', hA, hB])
  let e : ↥B ≃ ↥B' := (splitFinsetEquiv hAB).trans
    ((Equiv.sumCongr e₁ e₂).trans (splitFinsetEquiv hAB').symm)
  let σ : Equiv.Perm I := e.extendSubtype
  have hσB : ∀ v (hv : v ∈ B), σ v = (e ⟨v, hv⟩).1 := fun v hv ↦
    Equiv.extendSubtype_apply_of_mem e v hv
  have hmapB : B.map σ.toEmbedding = B' := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
      exact Equiv.extendSubtype_mem e v hv
    · rw [Finset.card_map, hB]
  have hmapA : A.map σ.toEmbedding = A' := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
      change σ v ∈ A'
      rw [hσB v (hAB hv)]
      simp only [e, Equiv.trans_apply]
      rw [splitFinsetEquiv_apply_of_mem hAB _ hv]
      simp [splitFinsetEquiv]
    · rw [Finset.card_map, hA]
  exact ⟨σ, hmapB, hmapA⟩

/-- **Exchangeability**: `E_{ρ_B}[phi W B A]` depends only on `|B|` and `|A|`. -/
theorem integral_nb_mul_phi_perm (W : Graphon Ω μ) {B A B' A' : Finset I} (hAB : A ⊆ B)
    (hAB' : A' ⊆ B') (hB : B.card = B'.card) (hA : A.card = A'.card) :
    ∫ x, nb W B x * phi W B A x ∂Measure.pi (fun _ : I ↦ μ) =
      ∫ x, nb W B' x * phi W B' A' x ∂Measure.pi (fun _ : I ↦ μ) := by
  obtain ⟨σ, hσB, hσA⟩ := exists_perm_map hAB hAB' hB hA
  rw [← integral_comp_perm (μ := μ) σ (fun x ↦ nb W B x * phi W B A x)]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show nb W B (fun v ↦ y (σ v)) * phi W B A (fun v ↦ y (σ v)) = nb W B' y * phi W B' A' y
  rw [nb_comp_perm, phi_comp_perm, hσB, hσA]

end Taeyoung.Paper.Profile
