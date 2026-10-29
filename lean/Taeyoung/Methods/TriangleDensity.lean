import Taeyoung.Methods.Peeling
import Taeyoung.Methods.Link.WeightedGoodmanRpow

/-!
# Triangle density: peeling and Goodman's bound

* `cliqueDensity_three_eq` — the triangle density peels to the triple
  integral, hence equals `∫ τ` (`cliqueDensity_three_eq_integral_rootedTriangle`);
* `goodman_triangle_bound` — Goodman's bound `t(K₃,W) ≥ p(2p-1)`, valid at
  every density.

The sharp bound of Fisher on `1/2 < p ≤ 2/3` is in
`Taeyoung/Methods/TriangleDensity/Fisher.lean`.
-/

open MeasureTheory

namespace Taeyoung.Methods.TriangleDensity

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The triangle density as a triple integral -/

lemma edgeFinset_top3 :
    (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_top3 (W : Graphon Ω μ) (x : Fin 3 → Ω) :
    graphWeight (⊤ : SimpleGraph (Fin 3)) W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) := by
  rw [graphWeight, edgeFinset_top3]
  simp
  ring

/-- **The triangle density, peeled.** -/
theorem cliqueDensity_three_eq (W : Graphon Ω μ) :
    cliqueDensity 3 W =
      ∫ a0, ∫ a1, ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ ∂μ ∂μ := by
  have hm : Measurable fun y : Fin 3 → Ω ↦
      W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) :=
    ((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
      (measurable_coord_pair W 1 2)
  have hb : ∀ y : Fin 3 → Ω, |W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2)| ≤ 1 := by
    intro y
    have h0 : 0 ≤ W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) :=
      mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (W.nonneg _ _)
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
      (W.nonneg _ _) (W.le_one _ _)
  rw [cliqueDensity, homDensity,
    integral_congr_ae (ae_of_all _ fun y ↦ graphWeight_top3 W y)]
  exact integral_assignment_fin_three
    (g := fun a0 a1 a2 ↦ W a0 a1 * W a0 a2 * W a1 a2) hm hb

/-- The triangle density is the mean of the rooted triangle density. -/
theorem cliqueDensity_three_eq_integral_rootedTriangle (W : Graphon Ω μ) :
    cliqueDensity 3 W = ∫ x, rootedTriangle W x ∂μ := by
  rw [cliqueDensity_three_eq]
  rfl

/-! ### Goodman's bound -/

/-- **Goodman's triangle bound**, `t(K₃,W) ≥ p(2p-1)`, at every density.  This
is the weighted rooted-triangle inequality at exponent `0`, divided by `p`. -/
theorem goodman_triangle_bound (W : Graphon Ω μ) (hp : 0 < cliqueDensity 2 W) :
    cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ≤ cliqueDensity 3 W := by
  set p := cliqueDensity 2 W with hpdef
  have hjen : p ^ ((0 : ℝ) + 2) ≤ momentR W ((0 : ℝ) + 2) :=
    rpow_le_momentR W (by norm_num)
  have hwt := weighted_rootedTriangle_rpow W (s := (0 : ℝ)) le_rfl
  have hzero : (∫ x, degree W x ^ (0 : ℝ) * rootedTriangle W x ∂μ)
      = cliqueDensity 3 W := by
    rw [cliqueDensity_three_eq_integral_rootedTriangle]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    show degree W x ^ (0 : ℝ) * rootedTriangle W x = rootedTriangle W x
    rw [Real.rpow_zero, one_mul]
  rw [hzero] at hwt
  rcases le_or_gt (2 * p - 1) 0 with h2p | h2p
  · have h3 : 0 ≤ cliqueDensity 3 W := by
      rw [cliqueDensity_three_eq_integral_rootedTriangle]
      exact integral_nonneg fun x ↦ rootedTriangle_nonneg W x
    nlinarith
  · have hstep : (2 * p - 1) * p ^ ((0 : ℝ) + 2) ≤ p * cliqueDensity 3 W :=
      le_trans (mul_le_mul_of_nonneg_left hjen h2p.le) hwt
    have hsq : p ^ ((0 : ℝ) + 2) = p ^ 2 := by
      rw [show (0 : ℝ) + 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hsq] at hstep
    have : p * (p * (2 * p - 1)) ≤ p * cliqueDensity 3 W := by nlinarith [hstep]
    exact le_of_mul_le_mul_left this hp

end Taeyoung.Methods.TriangleDensity
