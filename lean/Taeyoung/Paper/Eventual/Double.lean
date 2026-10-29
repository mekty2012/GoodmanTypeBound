import Taeyoung.Paper.Eventual.L2

/-!
# Bounded measurable kernels and their double integrals

Bookkeeping for the kernel computations of Theorem 1.6: a bounded
measurable two-variable function (`Bdd2`) has integrable rows, a bounded
measurable row-integral, and a double integral `dint` that is monotone, linear,
and symmetric under exchanging the variables (Fubini).
-/

open MeasureTheory

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded measurable kernel. -/
def Bdd2 (f : Ω → Ω → ℝ) : Prop := Measurable (Function.uncurry f) ∧ ∃ C, ∀ a b, |f a b| ≤ C

namespace Bdd2

variable {f g : Ω → Ω → ℝ}

lemma row (hf : Bdd2 f) (a : Ω) : IsBdd (f a) :=
  ⟨hf.1.comp (measurable_const.prodMk measurable_id), hf.2.choose, fun b ↦ hf.2.choose_spec a b⟩

lemma col (hf : Bdd2 f) (b : Ω) : IsBdd (fun a ↦ f a b) :=
  ⟨hf.1.comp (measurable_id.prodMk measurable_const), hf.2.choose, fun a ↦ hf.2.choose_spec a b⟩

lemma swap (hf : Bdd2 f) : Bdd2 (fun a b ↦ f b a) :=
  ⟨hf.1.comp (measurable_snd.prodMk measurable_fst), hf.2.choose,
    fun a b ↦ hf.2.choose_spec b a⟩

lemma integrable_prod (hf : Bdd2 f) : Integrable (Function.uncurry f) (μ.prod μ) :=
  (integrable_const hf.2.choose).mono' hf.1.aestronglyMeasurable
    (ae_of_all _ fun p ↦ by rw [Real.norm_eq_abs]; exact hf.2.choose_spec p.1 p.2)

lemma inner (hf : Bdd2 f) : IsBdd (fun a ↦ ∫ b, f a b ∂μ) := by
  refine ⟨(hf.1.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable, hf.2.choose,
    fun a ↦ ?_⟩
  calc |∫ b, f a b ∂μ| ≤ ∫ b, |f a b| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _b, hf.2.choose ∂μ :=
        integral_mono ((hf.row a).integrable.abs) (integrable_const _)
          fun b ↦ hf.2.choose_spec a b
    _ = hf.2.choose := by simp

lemma add (hf : Bdd2 f) (hg : Bdd2 g) : Bdd2 (fun a b ↦ f a b + g a b) :=
  ⟨hf.1.add hg.1, hf.2.choose + hg.2.choose, fun a b ↦
    (abs_add_le _ _).trans (add_le_add (hf.2.choose_spec a b) (hg.2.choose_spec a b))⟩

lemma mul (hf : Bdd2 f) (hg : Bdd2 g) : Bdd2 (fun a b ↦ f a b * g a b) := by
  refine ⟨hf.1.mul hg.1, hf.2.choose * hg.2.choose, fun a b ↦ ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf.2.choose_spec a b) (hg.2.choose_spec a b) (abs_nonneg _)
    ((abs_nonneg _).trans (hf.2.choose_spec a b))

lemma const (c : ℝ) : Bdd2 (fun _ _ : Ω ↦ c) := ⟨measurable_const, |c|, fun _ _ ↦ le_rfl⟩

lemma smul (c : ℝ) (hf : Bdd2 f) : Bdd2 (fun a b ↦ c * f a b) := (const c).mul hf

lemma sub (hf : Bdd2 f) (hg : Bdd2 g) : Bdd2 (fun a b ↦ f a b - g a b) := by
  have := hf.add (smul (-1) hg)
  simpa [sub_eq_add_neg] using this

lemma graphon (U : Graphon Ω μ) : Bdd2 (fun a b ↦ U a b) :=
  ⟨U.measurable, 1, fun a b ↦ by rw [abs_of_nonneg (U.nonneg a b)]; exact U.le_one a b⟩

lemma left {h : Ω → ℝ} (hh : IsBdd h) : Bdd2 (fun a _ ↦ h a) :=
  ⟨hh.1.comp measurable_fst, hh.2.choose, fun a _ ↦ hh.2.choose_spec a⟩

lemma right {h : Ω → ℝ} (hh : IsBdd h) : Bdd2 (fun _ b ↦ h b) :=
  ⟨hh.1.comp measurable_snd, hh.2.choose, fun _ b ↦ hh.2.choose_spec b⟩

end Bdd2

/-- The double integral `∫∫ f`. -/
noncomputable def dint (μ : Measure Ω) (f : Ω → Ω → ℝ) : ℝ := ∫ a, ∫ b, f a b ∂μ ∂μ

lemma dint_mono {f g : Ω → Ω → ℝ} (hf : Bdd2 f) (hg : Bdd2 g) (h : ∀ a b, f a b ≤ g a b) :
    dint μ f ≤ dint μ g :=
  integral_mono hf.inner.integrable hg.inner.integrable fun a ↦
    integral_mono (hf.row a).integrable (hg.row a).integrable (h a)

lemma dint_add {f g : Ω → Ω → ℝ} (hf : Bdd2 f) (hg : Bdd2 g) :
    dint μ (fun a b ↦ f a b + g a b) = dint μ f + dint μ g := by
  unfold dint
  have h1 : ∀ a, ∫ b, (f a b + g a b) ∂μ = (∫ b, f a b ∂μ) + ∫ b, g a b ∂μ := fun a ↦
    integral_add (hf.row a).integrable (hg.row a).integrable
  simp_rw [h1]
  exact integral_add hf.inner.integrable hg.inner.integrable

lemma dint_smul (c : ℝ) (f : Ω → Ω → ℝ) : dint μ (fun a b ↦ c * f a b) = c * dint μ f := by
  unfold dint
  simp_rw [integral_const_mul]

lemma dint_sub {f g : Ω → Ω → ℝ} (hf : Bdd2 f) (hg : Bdd2 g) :
    dint μ (fun a b ↦ f a b - g a b) = dint μ f - dint μ g := by
  have := dint_add (μ := μ) hf (Bdd2.smul (-1) hg)
  rw [dint_smul] at this
  have h : (fun a b ↦ f a b - g a b) = fun a b ↦ f a b + -1 * g a b := by
    funext a b; ring
  rw [h, this]; ring

lemma dint_swap {f : Ω → Ω → ℝ} (hf : Bdd2 f) :
    dint μ f = ∫ b, ∫ a, f a b ∂μ ∂μ :=
  integral_integral_swap hf.integrable_prod

lemma dint_nonneg {f : Ω → Ω → ℝ} (h : ∀ a b, 0 ≤ f a b) : 0 ≤ dint μ f :=
  integral_nonneg fun a ↦ integral_nonneg fun b ↦ h a b

/-- A parametric integral of a bounded measurable function of three variables. -/
lemma Bdd2.of_integral {G : Ω → Ω → Ω → ℝ}
    (hG : Measurable fun p : (Ω × Ω) × Ω ↦ G p.1.1 p.1.2 p.2) (C : ℝ)
    (hC : ∀ a b z, |G a b z| ≤ C) : Bdd2 (fun a b ↦ ∫ z, G a b z ∂μ) := by
  refine ⟨?_, C, fun a b ↦ ?_⟩
  · have := (hG.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
    exact this
  · have hi : Integrable (fun z ↦ G a b z) μ :=
      (integrable_const C).mono' (hG.comp (measurable_const.prodMk measurable_id :
        Measurable fun z : Ω ↦ ((a, b), z))).aestronglyMeasurable
        (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hC a b z)
    calc |∫ z, G a b z ∂μ| ≤ ∫ z, |G a b z| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _z, C ∂μ := integral_mono hi.abs (integrable_const _) fun z ↦ hC a b z
      _ = C := by simp

end Taeyoung.Paper.Eventual
