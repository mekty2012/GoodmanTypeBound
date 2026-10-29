import Taeyoung.Paper.Eventual.Integration
import Mathlib.Data.Nat.Choose.Cast

/-!
# Second-order control of tree densities (`paper.pdf`, Lemma 4.4)

Write `d` for the degree function of a graphon `U`, `q = ∫ d`, and
`X = ∫ (d - q)²`, and suppose `d ≤ Δ` pointwise.  Lemma 4.4 says
that every forest density `t(F,U)` with `r` edges is within
`C(r,2) Δ^{r-2} X` of `q^r`.

The paper deduces this from Sidorenko's tree inequalities (Lemma 4.3) and
(4.9).  Here we prove it
directly, by integrating leaves.  Integrating a leaf replaces the weight at its
neighbour by `φ_u · (Uφ_ℓ)`; we track, for every vertex weight `φ` that has
absorbed `k` edges (`GoodWeight k φ`):

* `0 ≤ φ ≤ Δ^k`;
* the `L²` distance to `q^k` is at most `k Δ^{k-1} √X`;
* the mean is within `C(k,2) Δ^{k-2} X` of `q^k`.

`GoodWeight.step` shows these are preserved; the second-order bound on the
mean uses that the first-order terms cancel (`∫ (d - q) = 0`).  To avoid
natural-number subtraction the bounds are stated multiplied by `Δ` and `Δ²`.

This file also contains the elementary `L²` facts used: Cauchy–Schwarz,
Minkowski, and `‖Uβ‖₂ ≤ Δ ‖β‖₂`.
-/

open MeasureTheory Finset

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Integrability of bounded functions -/

lemma integrable_of_abs_le {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ x, |f x| ≤ C) :
    Integrable f μ :=
  (integrable_const (μ := μ) C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact h x)

/-- A measurable function with a uniform bound. -/
def IsBdd (f : Ω → ℝ) : Prop := Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C

namespace IsBdd

lemma integrable {f : Ω → ℝ} (hf : IsBdd f) : Integrable f μ :=
  integrable_of_abs_le hf.1 hf.2.choose hf.2.choose_spec

lemma add {f g : Ω → ℝ} (hf : IsBdd f) (hg : IsBdd g) : IsBdd (fun x ↦ f x + g x) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  exact ⟨hfm.add hgm, C + D, fun x ↦ (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩

lemma neg {f : Ω → ℝ} (hf : IsBdd f) : IsBdd (fun x ↦ -f x) := by
  obtain ⟨hfm, C, hC⟩ := hf
  exact ⟨hfm.neg, C, fun x ↦ by rw [abs_neg]; exact hC x⟩

lemma sub {f g : Ω → ℝ} (hf : IsBdd f) (hg : IsBdd g) : IsBdd (fun x ↦ f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma mul {f g : Ω → ℝ} (hf : IsBdd f) (hg : IsBdd g) : IsBdd (fun x ↦ f x * g x) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  refine ⟨hfm.mul hgm, C * D, fun x ↦ ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))

lemma const (c : ℝ) : IsBdd (fun _ : Ω ↦ c) := ⟨measurable_const, |c|, fun _ ↦ le_rfl⟩

lemma of_bddFun (f : BddFun Ω) : IsBdd (f : Ω → ℝ) := ⟨f.measurable, f.bound, f.abs_le⟩

lemma sq {f : Ω → ℝ} (hf : IsBdd f) : IsBdd (fun x ↦ f x ^ 2) := by
  simpa [pow_two] using hf.mul hf

lemma smul (c : ℝ) {f : Ω → ℝ} (hf : IsBdd f) : IsBdd (fun x ↦ c * f x) :=
  (const c).mul hf

end IsBdd

/-- `∫ (A + s B + t C) = ∫ A + s ∫ B + t ∫ C`. -/
lemma integral_lin3 {A B C : Ω → ℝ} (hA : Integrable A μ) (hB : Integrable B μ)
    (hC : Integrable C μ) (s t : ℝ) :
    ∫ x, (A x + s * B x + t * C x) ∂μ = (∫ x, A x ∂μ) + s * (∫ x, B x ∂μ) + t * ∫ x, C x ∂μ := by
  have h1 : Integrable (fun x ↦ A x + s * B x) μ := hA.add (hB.const_mul s)
  have h2 : Integrable (fun x ↦ t * C x) μ := hC.const_mul t
  have h3 : Integrable (fun x ↦ s * B x) μ := hB.const_mul s
  rw [integral_add h1 h2, integral_add hA h3, integral_const_mul, integral_const_mul]

/-- `∫ (r A + s B + t C + D) = r ∫ A + s ∫ B + t ∫ C + ∫ D`. -/
lemma integral_lin4 {A B C D : Ω → ℝ} (hA : Integrable A μ) (hB : Integrable B μ)
    (hC : Integrable C μ) (hD : Integrable D μ) (r s t : ℝ) :
    ∫ x, (r * A x + s * B x + t * C x + D x) ∂μ =
      r * (∫ x, A x ∂μ) + s * (∫ x, B x ∂μ) + t * (∫ x, C x ∂μ) + ∫ x, D x ∂μ := by
  have h1 : Integrable (fun x ↦ r * A x + s * B x + t * C x) μ :=
    ((hA.const_mul r).add (hB.const_mul s)).add (hC.const_mul t)
  have h2 : Integrable (fun x ↦ r * A x + s * B x) μ := (hA.const_mul r).add (hB.const_mul s)
  have h3 : Integrable (fun x ↦ t * C x) μ := hC.const_mul t
  have h4 : Integrable (fun x ↦ r * A x) μ := hA.const_mul r
  have h5 : Integrable (fun x ↦ s * B x) μ := hB.const_mul s
  rw [integral_add h1 hD, integral_add h2 h3, integral_add h4 h5, integral_const_mul,
    integral_const_mul, integral_const_mul]

/-! ### `L²` norms -/

variable (μ) in
/-- The `L²(μ)` norm. -/
noncomputable def nrm (f : Ω → ℝ) : ℝ := Real.sqrt (∫ x, f x ^ 2 ∂μ)

lemma nrm_nonneg (f : Ω → ℝ) : 0 ≤ nrm μ f := Real.sqrt_nonneg _

lemma integral_sq_nonneg (f : Ω → ℝ) : 0 ≤ ∫ x, f x ^ 2 ∂μ :=
  integral_nonneg fun x ↦ sq_nonneg _

lemma nrm_sq (f : Ω → ℝ) : nrm μ f ^ 2 = ∫ x, f x ^ 2 ∂μ :=
  Real.sq_sqrt (integral_sq_nonneg f)

/-- The discriminant of a nonnegative quadratic. -/
lemma sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C) : B ^ 2 ≤ A * C := by
  rcases hC.lt_or_eq with hC | hC
  · have := h (B / C)
    have h2 : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by
      field_simp; ring
    rw [h2] at this
    have : B ^ 2 / C ≤ A := by linarith
    rwa [div_le_iff₀ hC] at this
  · subst hC
    by_cases hB : B = 0
    · subst hB; simp
    · exfalso
      have := h ((A + 1) / (2 * B))
      have h2 : A - 2 * ((A + 1) / (2 * B)) * B + ((A + 1) / (2 * B)) ^ 2 * 0 = -1 := by
        field_simp; ring
      linarith

/-- **Cauchy–Schwarz.** -/
lemma abs_integral_mul_le {f g : Ω → ℝ} (hf : IsBdd f) (hg : IsBdd g) :
    |∫ x, f x * g x ∂μ| ≤ nrm μ f * nrm μ g := by
  have hff := hf.sq.integrable (μ := μ)
  have hgg := hg.sq.integrable (μ := μ)
  have hfg := (hf.mul hg).integrable (μ := μ)
  have hq : ∀ t : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂μ) - 2 * t * (∫ x, f x * g x ∂μ) +
      t ^ 2 * ∫ x, g x ^ 2 ∂μ := by
    intro t
    have : (∫ x, (f x - t * g x) ^ 2 ∂μ) = (∫ x, f x ^ 2 ∂μ) -
        2 * t * (∫ x, f x * g x ∂μ) + t ^ 2 * ∫ x, g x ^ 2 ∂μ := by
      have h1 : (fun x ↦ (f x - t * g x) ^ 2) =
          fun x ↦ f x ^ 2 + (-(2 * t)) * (f x * g x) + t ^ 2 * g x ^ 2 := by
        funext x; ring
      rw [h1, integral_lin3 hff hfg hgg]
      ring
    rw [← this]
    exact integral_nonneg fun x ↦ sq_nonneg _
  have hd := sq_le_mul_of_quadratic_nonneg (integral_sq_nonneg g) hq
  rw [nrm, nrm, ← Real.sqrt_mul (integral_sq_nonneg f)]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hd

/-- **Minkowski.** -/
lemma nrm_add_le {f g : Ω → ℝ} (hf : IsBdd f) (hg : IsBdd g) :
    nrm μ (fun x ↦ f x + g x) ≤ nrm μ f + nrm μ g := by
  have hff := hf.sq.integrable (μ := μ)
  have hgg := hg.sq.integrable (μ := μ)
  have hfg := (hf.mul hg).integrable (μ := μ)
  have hcs := abs_integral_mul_le (μ := μ) hf hg
  have hexp : (∫ x, (f x + g x) ^ 2 ∂μ) = (∫ x, f x ^ 2 ∂μ) + 2 * (∫ x, f x * g x ∂μ) +
      ∫ x, g x ^ 2 ∂μ := by
    have h1 : (fun x ↦ (f x + g x) ^ 2) =
        fun x ↦ f x ^ 2 + 2 * (f x * g x) + 1 * g x ^ 2 := by
      funext x; ring
    rw [h1, integral_lin3 hff hfg hgg]
    ring
  have hle : (∫ x, (f x + g x) ^ 2 ∂μ) ≤ (nrm μ f + nrm μ g) ^ 2 := by
    rw [hexp, add_sq, nrm_sq, nrm_sq]
    have : ∫ x, f x * g x ∂μ ≤ nrm μ f * nrm μ g := (le_abs_self _).trans hcs
    nlinarith
  calc nrm μ (fun x ↦ f x + g x) ≤ Real.sqrt ((nrm μ f + nrm μ g) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = nrm μ f + nrm μ g := Real.sqrt_sq (add_nonneg (nrm_nonneg _) (nrm_nonneg _))

lemma nrm_congr {f g : Ω → ℝ} (h : ∀ x, f x = g x) : nrm μ f = nrm μ g := by
  simp only [nrm, h]

/-- `‖c f‖₂ = |c| ‖f‖₂`. -/
lemma nrm_smul (c : ℝ) (f : Ω → ℝ) : nrm μ (fun x ↦ c * f x) = |c| * nrm μ f := by
  unfold nrm
  have : (fun x ↦ (c * f x) ^ 2) = fun x ↦ c ^ 2 * f x ^ 2 := by funext x; ring
  rw [this, integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- A pointwise bound `|f| ≤ M` gives `‖f g‖₂ ≤ M ‖g‖₂`. -/
lemma nrm_mul_le {f g : Ω → ℝ} (hf : IsBdd f) (hg : IsBdd g) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, |f x| ≤ M) :
    nrm μ (fun x ↦ f x * g x) ≤ M * nrm μ g := by
  unfold nrm
  have hle : (∫ x, (f x * g x) ^ 2 ∂μ) ≤ ∫ x, M ^ 2 * g x ^ 2 ∂μ := by
    refine integral_mono (hf.mul hg).sq.integrable (hg.sq.integrable.const_mul _) fun x ↦ ?_
    simp only []
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  rw [integral_const_mul] at hle
  calc Real.sqrt (∫ x, (f x * g x) ^ 2 ∂μ) ≤ Real.sqrt (M ^ 2 * ∫ x, g x ^ 2 ∂μ) :=
        Real.sqrt_le_sqrt hle
    _ = M * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0]

/-! ### The graphon operator on bounded functions -/

section Operator

variable (U : Graphon Ω μ)

lemma isBdd_degree : IsBdd (degree U) :=
  ⟨measurable_degree U, 1, fun x ↦ by
    rw [abs_of_nonneg (degree_nonneg U x)]; exact degree_le_one U x⟩

lemma isBdd_row (x : Ω) : IsBdd (fun y ↦ U x y) :=
  ⟨U.measurable.comp (measurable_const.prodMk measurable_id), 1, fun y ↦ by
    rw [abs_of_nonneg (U.nonneg x y)]; exact U.le_one x y⟩

lemma isBdd_kernelApply {f : Ω → ℝ} (hf : IsBdd f) : IsBdd (kernelApply U f) := by
  obtain ⟨hfm, C, hC⟩ := hf
  exact IsBdd.of_bddFun (BddFun.apply U ⟨f, hfm, C, hC⟩)

lemma integrable_uncurry_mul {f : Ω → ℝ} (hf : IsBdd f) :
    Integrable (fun p : Ω × Ω ↦ U p.1 p.2 * f p.2) (μ.prod μ) := by
  obtain ⟨hfm, C, hC⟩ := hf
  refine (integrable_const (μ := μ.prod μ) C).mono'
    (U.measurable.mul (hfm.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (U.nonneg _ _)]
  calc U p.1 p.2 * |f p.2| ≤ 1 * C :=
        mul_le_mul (U.le_one _ _) (hC _) (abs_nonneg _) zero_le_one
    _ = C := one_mul C

/-- `∫ U f = ∫ d f`, by symmetry. -/
lemma integral_kernelApply {f : Ω → ℝ} (hf : IsBdd f) :
    ∫ x, kernelApply U f x ∂μ = ∫ y, degree U y * f y ∂μ := by
  unfold kernelApply
  rw [integral_integral_swap (integrable_uncurry_mul U hf)]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []
  rw [integral_mul_const]
  unfold degree
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x ↦ U.symm x y)

/-- Weighted Cauchy–Schwarz: `(∫ U(x,·) β)² ≤ d(x) ∫ U(x,·) β²`. -/
lemma sq_kernelApply_le {β : Ω → ℝ} (hβ : IsBdd β) (x : Ω) :
    kernelApply U β x ^ 2 ≤ degree U x * ∫ y, U x y * β y ^ 2 ∂μ := by
  have hU : IsBdd (fun y ↦ U x y) := isBdd_row U x
  have h1 := (hU.mul hβ).integrable (μ := μ)
  have h2 := (hU.mul hβ.sq).integrable (μ := μ)
  have h0 := hU.integrable (μ := μ)
  have hq : ∀ t : ℝ, 0 ≤ (∫ y, U x y * β y ^ 2 ∂μ) - 2 * t * kernelApply U β x +
      t ^ 2 * degree U x := by
    intro t
    have : (∫ y, U x y * (β y - t) ^ 2 ∂μ) = (∫ y, U x y * β y ^ 2 ∂μ) -
        2 * t * kernelApply U β x + t ^ 2 * degree U x := by
      have hfun : (fun y ↦ U x y * (β y - t) ^ 2) =
          fun y ↦ U x y * β y ^ 2 + (-(2 * t)) * (U x y * β y) + t ^ 2 * U x y := by
        funext y; ring
      rw [hfun, integral_lin3 h2 h1 h0]
      simp only [kernelApply, degree]
      ring
    rw [← this]
    exact integral_nonneg fun y ↦ mul_nonneg (U.nonneg _ _) (sq_nonneg _)
  have := sq_le_mul_of_quadratic_nonneg (degree_nonneg U x) hq
  linarith

/-- **`‖Uβ‖₂ ≤ Δ ‖β‖₂`** when `d ≤ Δ`. -/
lemma nrm_kernelApply_le {Δ : ℝ} (hΔ0 : 0 ≤ Δ) (hΔ : ∀ x, degree U x ≤ Δ) {β : Ω → ℝ}
    (hβ : IsBdd β) :
    nrm μ (kernelApply U β) ≤ Δ * nrm μ β := by
  have hint : Integrable (fun p : Ω × Ω ↦ U p.1 p.2 * β p.2 ^ 2) (μ.prod μ) :=
    integrable_uncurry_mul U hβ.sq
  have hG : IsBdd (fun x ↦ ∫ y, U x y * β y ^ 2 ∂μ) := by
    obtain ⟨hβm, C, hC⟩ := hβ.sq
    exact IsBdd.of_bddFun (BddFun.apply U ⟨_, hβm, C, hC⟩)
  have h1 : (∫ x, kernelApply U β x ^ 2 ∂μ) ≤ ∫ x, Δ * ∫ y, U x y * β y ^ 2 ∂μ ∂μ := by
    refine integral_mono (isBdd_kernelApply U hβ).sq.integrable
      (hG.integrable.const_mul _) fun x ↦ ?_
    refine (sq_kernelApply_le U hβ x).trans ?_
    exact mul_le_mul_of_nonneg_right (hΔ x)
      (integral_nonneg fun y ↦ mul_nonneg (U.nonneg _ _) (sq_nonneg _))
  have h2 : (∫ x, ∫ y, U x y * β y ^ 2 ∂μ ∂μ) = ∫ y, degree U y * β y ^ 2 ∂μ := by
    have := integral_kernelApply U hβ.sq
    simpa [kernelApply] using this
  have h3 : (∫ y, degree U y * β y ^ 2 ∂μ) ≤ ∫ y, Δ * β y ^ 2 ∂μ :=
    integral_mono ((isBdd_degree U).mul hβ.sq).integrable (hβ.sq.integrable.const_mul _)
      fun y ↦ mul_le_mul_of_nonneg_right (hΔ y) (sq_nonneg _)
  rw [integral_const_mul, h2] at h1
  rw [integral_const_mul] at h3
  have hsq : (∫ x, kernelApply U β x ^ 2 ∂μ) ≤ Δ ^ 2 * ∫ y, β y ^ 2 ∂μ := by
    nlinarith
  calc nrm μ (kernelApply U β) ≤ Real.sqrt (Δ ^ 2 * ∫ y, β y ^ 2 ∂μ) :=
        Real.sqrt_le_sqrt hsq
    _ = Δ * nrm μ β := by
        rw [Real.sqrt_mul (sq_nonneg Δ), Real.sqrt_sq hΔ0]; rfl

end Operator

/-! ### Weights of degree `k` -/

section Weights

variable (U : Graphon Ω μ)

/-- `q = ∫ d`. -/
noncomputable def meanDeg : ℝ := ∫ x, degree U x ∂μ

/-- `X = ∫ (d - q)²`. -/
noncomputable def degVar : ℝ := ∫ x, (degree U x - meanDeg U) ^ 2 ∂μ

lemma meanDeg_nonneg : 0 ≤ meanDeg U := integral_nonneg fun x ↦ degree_nonneg U x

lemma degVar_nonneg : 0 ≤ degVar U := integral_nonneg fun x ↦ sq_nonneg _

lemma meanDeg_le {Δ : ℝ} (hΔ : ∀ x, degree U x ≤ Δ) : meanDeg U ≤ Δ := by
  unfold meanDeg
  calc ∫ x, degree U x ∂μ ≤ ∫ _x, Δ ∂μ :=
        integral_mono (isBdd_degree U).integrable (integrable_const _) hΔ
    _ = Δ := by simp

/-- A vertex weight that has absorbed `k` edges. -/
structure GoodWeight (Δ : ℝ) (k : ℕ) (φ : BddFun Ω) : Prop where
  nonneg : ∀ y, 0 ≤ φ y
  le : ∀ y, φ y ≤ Δ ^ k
  nrm_le : Δ * nrm μ (fun y ↦ φ y - meanDeg U ^ k) ≤ k * Δ ^ k * Real.sqrt (degVar U)
  mean_le : Δ ^ 2 * |∫ y, φ y ∂μ - meanDeg U ^ k| ≤ (k.choose 2 : ℝ) * Δ ^ k * degVar U

lemma goodWeight_one (Δ : ℝ) : GoodWeight U Δ 0 BddFun.one := by
  refine ⟨fun _ ↦ zero_le_one, fun _ ↦ by simp, ?_, ?_⟩
  · simp [nrm]
  · simp

variable {U}

lemma GoodWeight.abs_integral_le {Δ : ℝ} {k : ℕ} {φ : BddFun Ω} (h : GoodWeight U Δ k φ) :
    |∫ y, φ y ∂μ| ≤ Δ ^ k := by
  rw [abs_of_nonneg (integral_nonneg h.nonneg)]
  calc ∫ y, φ y ∂μ ≤ ∫ _y, Δ ^ k ∂μ := integral_mono φ.integrable (integrable_const _) h.le
    _ = Δ ^ k := by simp

lemma Nat_choose_two_succ_add (a b : ℕ) :
    ((a + b + 1).choose 2 : ℝ) = a.choose 2 + b.choose 2 + a + b + a * b := by
  rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  ring

/-- **Integrating a leaf preserves the weight bounds.**  If `φ` has absorbed `a`
edges and `ψ` has absorbed `b`, then `φ · (Uψ)` has absorbed `a + b + 1`. -/
theorem GoodWeight.step {Δ : ℝ} (hΔ : 0 < Δ) (hdeg : ∀ x, degree U x ≤ Δ) {a b : ℕ}
    {φ ψ : BddFun Ω} (hφ : GoodWeight U Δ a φ) (hψ : GoodWeight U Δ b ψ) :
    GoodWeight U Δ (a + b + 1) (φ.mul (BddFun.apply U ψ)) := by
  set q := meanDeg U with hq
  set X := degVar U with hX
  have hq0 : 0 ≤ q := meanDeg_nonneg U
  have hqΔ : q ≤ Δ := meanDeg_le U hdeg
  have hX0 : 0 ≤ X := degVar_nonneg U
  have hsX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0
  have hφb := IsBdd.of_bddFun φ
  have hψb := IsBdd.of_bddFun ψ
  set α : Ω → ℝ := fun y ↦ φ y - q ^ a with hα
  set β : Ω → ℝ := fun y ↦ ψ y - q ^ b with hβ
  set δ : Ω → ℝ := fun y ↦ degree U y - q with hδ
  have hαb : IsBdd α := hφb.sub (IsBdd.const _)
  have hβb : IsBdd β := hψb.sub (IsBdd.const _)
  have hδb : IsBdd δ := (isBdd_degree U).sub (IsBdd.const _)
  have hTβ : IsBdd (kernelApply U β) := isBdd_kernelApply U hβb
  -- `Uψ = q^b d + Uβ`
  have hTψ : ∀ y, kernelApply U ψ y = q ^ b * degree U y + kernelApply U β y := by
    intro y
    unfold kernelApply degree
    have h1 : Integrable (fun z ↦ U y z) μ := (isBdd_row U y).integrable
    have h2 : Integrable (fun z ↦ U y z * β z) μ := integrable_kernel_mul U
      ⟨β, hβb.1, hβb.2.choose, hβb.2.choose_spec⟩ y
    rw [← integral_const_mul, ← integral_add (h1.const_mul _) h2]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [hβ]
    ring
  -- pointwise bounds on `Uψ`
  have hTψ0 : ∀ y, 0 ≤ kernelApply U ψ y := fun y ↦
    integral_nonneg fun z ↦ mul_nonneg (U.nonneg _ _) (hψ.nonneg z)
  have hTψle : ∀ y, kernelApply U ψ y ≤ Δ ^ (b + 1) := by
    intro y
    have hle : kernelApply U ψ y ≤ ∫ z, U y z * Δ ^ b ∂μ := by
      refine integral_mono (integrable_kernel_mul U ψ y) ?_ fun z ↦ ?_
      · exact (integrable_kernel_mul U (BddFun.const (Δ ^ b)) y)
      · exact mul_le_mul_of_nonneg_left (hψ.le z) (U.nonneg _ _)
    rw [integral_mul_const] at hle
    calc kernelApply U ψ y ≤ degree U y * Δ ^ b := hle
      _ ≤ Δ * Δ ^ b := mul_le_mul_of_nonneg_right (hdeg y) (pow_nonneg hΔ.le _)
      _ = Δ ^ (b + 1) := by ring
  refine ⟨fun y ↦ mul_nonneg (hφ.nonneg y) (hTψ0 y), fun y ↦ ?_, ?_, ?_⟩
  · -- the sup bound
    show φ y * kernelApply U ψ y ≤ Δ ^ (a + b + 1)
    calc φ y * kernelApply U ψ y ≤ Δ ^ a * Δ ^ (b + 1) :=
          mul_le_mul (hφ.le y) (hTψle y) (hTψ0 y) (pow_nonneg hΔ.le _)
      _ = Δ ^ (a + b + 1) := by ring
  · -- the `L²` bound
    have hnβ := hψ.nrm_le
    have hnα := hφ.nrm_le
    -- `‖Uψ - q^{b+1}‖ ≤ Δ‖β‖ + q^b √X`
    have hA : nrm μ (fun y ↦ kernelApply U ψ y - q ^ (b + 1)) ≤
        Δ * nrm μ β + q ^ b * Real.sqrt X := by
      have hsplit : ∀ y, kernelApply U ψ y - q ^ (b + 1) = kernelApply U β y + q ^ b * δ y := by
        intro y; rw [hTψ y]; simp only [hδ]; ring
      rw [nrm_congr hsplit]
      refine (nrm_add_le hTβ ((IsBdd.const _).mul hδb)).trans (add_le_add ?_ ?_)
      · exact nrm_kernelApply_le U hΔ.le hdeg hβb
      · rw [nrm_smul, abs_of_nonneg (pow_nonneg hq0 _)]
        exact le_rfl
    have hsplit : ∀ y, (φ.mul (BddFun.apply U ψ)) y - q ^ (a + b + 1) =
        φ y * (kernelApply U ψ y - q ^ (b + 1)) + q ^ (b + 1) * α y := by
      intro y
      show φ y * kernelApply U ψ y - q ^ (a + b + 1) = _
      simp only [hα]; ring
    rw [nrm_congr hsplit]
    have hB : nrm μ (fun y ↦ φ y * (kernelApply U ψ y - q ^ (b + 1)) + q ^ (b + 1) * α y) ≤
        Δ ^ a * (Δ * nrm μ β + q ^ b * Real.sqrt X) + q ^ (b + 1) * nrm μ α := by
      refine (nrm_add_le (hφb.mul ((isBdd_kernelApply U hψb).sub (IsBdd.const _)))
        ((IsBdd.const _).mul hαb)).trans (add_le_add ?_ ?_)
      · refine (nrm_mul_le hφb ((isBdd_kernelApply U hψb).sub (IsBdd.const _))
          (pow_nonneg hΔ.le _) fun y ↦ ?_).trans
          (mul_le_mul_of_nonneg_left hA (pow_nonneg hΔ.le _))
        rw [abs_of_nonneg (hφ.nonneg y)]; exact hφ.le y
      · rw [nrm_smul, abs_of_nonneg (pow_nonneg hq0 _)]
    have hqb : q ^ b ≤ Δ ^ b := pow_le_pow_left₀ hq0 hqΔ b
    have hqb1 : q ^ (b + 1) ≤ Δ ^ (b + 1) := pow_le_pow_left₀ hq0 hqΔ (b + 1)
    have hnα0 : 0 ≤ nrm μ α := nrm_nonneg _
    have hnβ0 : 0 ≤ nrm μ β := nrm_nonneg _
    have hsX0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
    have hΔa : 0 ≤ Δ ^ a := pow_nonneg hΔ.le _
    calc Δ * nrm μ (fun y ↦ φ y * (kernelApply U ψ y - q ^ (b + 1)) + q ^ (b + 1) * α y)
        ≤ Δ * (Δ ^ a * (Δ * nrm μ β + q ^ b * Real.sqrt X) + q ^ (b + 1) * nrm μ α) :=
          mul_le_mul_of_nonneg_left hB hΔ.le
      _ = Δ ^ a * Δ * (Δ * nrm μ β) + Δ ^ a * Δ * q ^ b * Real.sqrt X +
            q ^ (b + 1) * (Δ * nrm μ α) := by ring
      _ ≤ Δ ^ a * Δ * (b * Δ ^ b * Real.sqrt X) + Δ ^ a * Δ * Δ ^ b * Real.sqrt X +
            Δ ^ (b + 1) * (a * Δ ^ a * Real.sqrt X) := by
          gcongr
      _ = ((a + b + 1 : ℕ) : ℝ) * Δ ^ (a + b + 1) * Real.sqrt X := by
          push_cast; ring
  · -- the second-order bound on the mean
    have hmα := hφ.mean_le
    have hmβ := hψ.mean_le
    have hnα := hφ.nrm_le
    have hnβ := hψ.nrm_le
    have hφi := φ.integrable (μ := μ)
    have hψi := ψ.integrable (μ := μ)
    have hdi := (isBdd_degree U).integrable (μ := μ)
    -- the exact expansion of the mean
    have hexp : ∫ y, (φ.mul (BddFun.apply U ψ)) y ∂μ - q ^ (a + b + 1) =
        q ^ (b + 1) * (∫ y, φ y ∂μ - q ^ a) + q ^ (a + 1) * (∫ y, ψ y ∂μ - q ^ b) +
          q ^ a * (∫ y, δ y * β y ∂μ) + q ^ b * (∫ y, α y * δ y ∂μ) +
            ∫ y, α y * kernelApply U β y ∂μ := by
      have hpt : ∀ y, (φ.mul (BddFun.apply U ψ)) y =
          q ^ (a + b) * degree U y + q ^ a * kernelApply U β y +
            q ^ b * (α y * degree U y) + α y * kernelApply U β y := by
        intro y
        show φ y * kernelApply U ψ y = _
        rw [hTψ y]; simp only [hα]; ring
      have hαd := (hαb.mul (isBdd_degree U)).integrable (μ := μ)
      have hαT := (hαb.mul hTβ).integrable (μ := μ)
      have hTi := hTβ.integrable (μ := μ)
      rw [integral_congr_ae (ae_of_all _ hpt)]
      rw [integral_lin4 hdi hTi hαd hαT]
      -- `∫ U β = ∫ d β = q ∫ β + ∫ δ β` and `∫ α d = q ∫ α + ∫ α δ`
      have hUβ : ∫ y, kernelApply U β y ∂μ = q * ∫ y, β y ∂μ + ∫ y, δ y * β y ∂μ := by
        rw [integral_kernelApply U hβb, ← integral_const_mul,
          ← integral_add (hβb.integrable.const_mul _) (hδb.mul hβb).integrable]
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        simp only [hδ]; ring
      have hαδ : ∫ y, α y * degree U y ∂μ = q * ∫ y, α y ∂μ + ∫ y, α y * δ y ∂μ := by
        rw [← integral_const_mul, ← integral_add (hαb.integrable.const_mul _)
          (hαb.mul hδb).integrable]
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        simp only [hδ]; ring
      have hβi : ∫ y, β y ∂μ = ∫ y, ψ y ∂μ - q ^ b := by
        rw [hβ, integral_sub hψi (integrable_const _)]; simp
      have hαi : ∫ y, α y ∂μ = ∫ y, φ y ∂μ - q ^ a := by
        rw [hα, integral_sub hφi (integrable_const _)]; simp
      have hd : ∫ y, degree U y ∂μ = q := rfl
      rw [hUβ, hαδ, hβi, hαi, hd]
      ring
    have hqa : q ^ a ≤ Δ ^ a := pow_le_pow_left₀ hq0 hqΔ a
    have hqb : q ^ b ≤ Δ ^ b := pow_le_pow_left₀ hq0 hqΔ b
    have hqa1 : q ^ (a + 1) ≤ Δ ^ (a + 1) := pow_le_pow_left₀ hq0 hqΔ _
    have hqb1 : q ^ (b + 1) ≤ Δ ^ (b + 1) := pow_le_pow_left₀ hq0 hqΔ _
    have hnα0 : 0 ≤ nrm μ α := nrm_nonneg _
    have hnβ0 : 0 ≤ nrm μ β := nrm_nonneg _
    have hsX0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
    have hc1 : |∫ y, δ y * β y ∂μ| ≤ Real.sqrt X * nrm μ β := abs_integral_mul_le hδb hβb
    have hc2 : |∫ y, α y * δ y ∂μ| ≤ nrm μ α * Real.sqrt X := abs_integral_mul_le hαb hδb
    have hc3 : |∫ y, α y * kernelApply U β y ∂μ| ≤ nrm μ α * (Δ * nrm μ β) :=
      (abs_integral_mul_le hαb hTβ).trans
        (mul_le_mul_of_nonneg_left (nrm_kernelApply_le U hΔ.le hdeg hβb) hnα0)
    rw [hexp]
    have htri : |q ^ (b + 1) * (∫ y, φ y ∂μ - q ^ a) + q ^ (a + 1) * (∫ y, ψ y ∂μ - q ^ b) +
          q ^ a * (∫ y, δ y * β y ∂μ) + q ^ b * (∫ y, α y * δ y ∂μ) +
            ∫ y, α y * kernelApply U β y ∂μ| ≤
        q ^ (b + 1) * |∫ y, φ y ∂μ - q ^ a| + q ^ (a + 1) * |∫ y, ψ y ∂μ - q ^ b| +
          q ^ a * |∫ y, δ y * β y ∂μ| + q ^ b * |∫ y, α y * δ y ∂μ| +
            |∫ y, α y * kernelApply U β y ∂μ| := by
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      all_goals rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
    calc Δ ^ 2 * |q ^ (b + 1) * (∫ y, φ y ∂μ - q ^ a) + q ^ (a + 1) * (∫ y, ψ y ∂μ - q ^ b) +
          q ^ a * (∫ y, δ y * β y ∂μ) + q ^ b * (∫ y, α y * δ y ∂μ) +
            ∫ y, α y * kernelApply U β y ∂μ|
        ≤ Δ ^ 2 * (q ^ (b + 1) * |∫ y, φ y ∂μ - q ^ a| +
            q ^ (a + 1) * |∫ y, ψ y ∂μ - q ^ b| +
          q ^ a * |∫ y, δ y * β y ∂μ| + q ^ b * |∫ y, α y * δ y ∂μ| +
            |∫ y, α y * kernelApply U β y ∂μ|) :=
          mul_le_mul_of_nonneg_left htri (sq_nonneg Δ)
      _ = q ^ (b + 1) * (Δ ^ 2 * |∫ y, φ y ∂μ - q ^ a|) +
            q ^ (a + 1) * (Δ ^ 2 * |∫ y, ψ y ∂μ - q ^ b|) +
          q ^ a * Δ ^ 2 * |∫ y, δ y * β y ∂μ| + q ^ b * Δ ^ 2 * |∫ y, α y * δ y ∂μ| +
            Δ ^ 2 * |∫ y, α y * kernelApply U β y ∂μ| := by ring
      _ ≤ Δ ^ (b + 1) * ((a.choose 2 : ℝ) * Δ ^ a * X) +
            Δ ^ (a + 1) * ((b.choose 2 : ℝ) * Δ ^ b * X) +
          Δ ^ a * Δ ^ 2 * (Real.sqrt X * nrm μ β) + Δ ^ b * Δ ^ 2 * (nrm μ α * Real.sqrt X) +
            Δ ^ 2 * (nrm μ α * (Δ * nrm μ β)) := by
          gcongr
      _ = Δ ^ (a + b + 1) * ((a.choose 2 : ℝ) + b.choose 2) * X +
            Δ ^ a * Δ * Real.sqrt X * (Δ * nrm μ β) + Δ ^ b * Δ * Real.sqrt X * (Δ * nrm μ α) +
            Δ * (Δ * nrm μ α) * (Δ * nrm μ β) := by ring
      _ ≤ Δ ^ (a + b + 1) * ((a.choose 2 : ℝ) + b.choose 2) * X +
            Δ ^ a * Δ * Real.sqrt X * (b * Δ ^ b * Real.sqrt X) +
            Δ ^ b * Δ * Real.sqrt X * (a * Δ ^ a * Real.sqrt X) +
            Δ * (a * Δ ^ a * Real.sqrt X) * (b * Δ ^ b * Real.sqrt X) := by
          have h1 : 0 ≤ Δ ^ a * Δ * Real.sqrt X := by positivity
          have h2 : 0 ≤ Δ ^ b * Δ * Real.sqrt X := by positivity
          have h3 : 0 ≤ Δ * nrm μ α := mul_nonneg hΔ.le hnα0
          have h4 : 0 ≤ (b : ℝ) * Δ ^ b * Real.sqrt X := by positivity
          gcongr
      _ = (((a + b + 1).choose 2 : ℕ) : ℝ) * Δ ^ (a + b + 1) * X := by
          rw [Nat_choose_two_succ_add]
          have : Real.sqrt X * Real.sqrt X = X := hsX
          linear_combination (Δ ^ (a + b + 1) * (b + a + a * b)) * this

end Weights

end Taeyoung.Paper.Eventual
