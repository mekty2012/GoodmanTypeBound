import Mathlib

/-!
# Graphons as integral kernels

A graphon is an unbundled kernel on an abstract probability space:

* `IsGraphon W μ`: `W : Ω → Ω → ℝ` is measurable, symmetric and `[0,1]`-valued;
* `Good f`: `f` is measurable and bounded;
* `kernelOp W μ f x = ∫ y, W x y * f y`, `mean μ f = ∫ f`;
* `degree = kernelOp 1` and `edgeDensity = mean degree`, the edge density `t(K₂, W)`.
-/

open MeasureTheory

namespace Taeyoung.Fisher

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A graphon (here, the complement kernel `U = 1 − W`): symmetric, measurable, `[0,1]`-valued. -/
structure IsGraphon (U : Ω → Ω → ℝ) (μ : Measure Ω) : Prop where
  meas : Measurable (Function.uncurry U)
  nonneg : ∀ x y, 0 ≤ U x y
  le_one : ∀ x y, U x y ≤ 1
  symm : ∀ x y, U x y = U y x

/-- Bounded, strongly measurable real functions: the working space. -/
structure Good (f : Ω → ℝ) : Prop where
  meas : StronglyMeasurable f
  bdd : ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C

lemma Good.integrable {f : Ω → ℝ} (hf : Good f) : Integrable f μ := by
  obtain ⟨C, _, hC⟩ := hf.bdd
  refine (integrable_const C).mono' hf.meas.aestronglyMeasurable (ae_of_all _ ?_)
  intro x; simpa [Real.norm_eq_abs] using hC x

lemma Good.mul {f k : Ω → ℝ} (hf : Good f) (hk : Good k) : Good (fun x => f x * k x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Ck, hCk0, hCk⟩ := hk.bdd
  refine ⟨hf.meas.mul hk.meas, ⟨Cf * Ck, mul_nonneg hCf0 hCk0, fun x => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hCf x) (hCk x) (abs_nonneg _) hCf0

lemma good_smul (c : ℝ) {f : Ω → ℝ} (hf : Good f) : Good (c • f) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨hf.meas.const_smul c, ⟨|c| * C, mul_nonneg (abs_nonneg _) hC0, fun x => ?_⟩⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

variable {U : Ω → Ω → ℝ}

/-- The kernel form `kernelOp U f x = ∫ y, U x y * f y`. -/
noncomputable def kernelOp (U : Ω → Ω → ℝ) (μ : Measure Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => ∫ y, U x y * f y ∂μ

/-- The mean of a function. -/
noncomputable def mean (μ : Measure Ω) (f : Ω → ℝ) : ℝ := ∫ x, f x ∂μ

lemma good_kernelOp (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) : Good (kernelOp U μ f) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨?_, ⟨C, hC0, fun x => ?_⟩⟩
  · have hSM : StronglyMeasurable (fun p : Ω × Ω => U p.1 p.2 * f p.2) :=
      (hU.meas.stronglyMeasurable).mul (hf.meas.comp_measurable measurable_snd)
    exact hSM.integral_prod_right'
  · have hmx : Measurable (fun y => U x y) := hU.meas.comp measurable_prodMk_left
    have hint : Integrable (fun y => U x y * f y) μ :=
      (Good.mul ⟨hmx.stronglyMeasurable, ⟨1, zero_le_one, fun y => by
        rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y⟩⟩ hf).integrable
    calc |kernelOp U μ f x| ≤ ∫ y, |U x y * f y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _y, C ∂μ := by
          refine integral_mono hint.abs (integrable_const C) (fun y => ?_)
          rw [abs_mul, abs_of_nonneg (hU.nonneg x y)]
          calc U x y * |f y| ≤ 1 * |f y| :=
                mul_le_mul_of_nonneg_right (hU.le_one x y) (abs_nonneg _)
            _ = |f y| := one_mul _
            _ ≤ C := hC y
      _ = C := by simp

/-- The degree function `degree = kernelOp 1`. -/
noncomputable def degree (U : Ω → Ω → ℝ) (μ : Measure Ω) : Ω → ℝ := fun x => ∫ y, U x y ∂μ

/-- The edge density of `U`, `edgeDensity = mean degree`. -/
noncomputable def edgeDensity (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℝ := mean μ (degree U μ)

lemma good_degree (hU : IsGraphon U μ) : Good (degree U μ) := by
  have h : degree U μ = kernelOp U μ (fun _ => 1) := by funext x; simp [degree, kernelOp]
  rw [h]; exact good_kernelOp hU ⟨stronglyMeasurable_const, ⟨1, zero_le_one, fun _ => by norm_num⟩⟩

end Taeyoung.Fisher
