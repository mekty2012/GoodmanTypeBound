import Taeyoung.Fisher
import Taeyoung.Methods.TriangleDensity

/-!
# Triangle density: Fisher's sharp bound, in this project's vocabulary

`Taeyoung/Fisher/` proves Fisher's theorem [Fisher, *Lower bounds on the number
of triangles in a graph*, J. Graph Theory 13 (1989)] on the band
`1/2 < p ≤ 2/3`.  It is stated there for an unbundled kernel
`W : Ω → Ω → ℝ` with a predicate `IsGraphon`, an `edgeDensity`, and the
triangle density written as `trace μ (compPow μ W 2)`.  This file restates it
for the bundled `Graphon Ω μ` of `Foundation/`:

* `edgeDensity_bridge`, `trace_compPow_bridge` — the two vocabularies agree,
  by Fubini;
* `fisher_triangle_bound` — the sharp bound `t(K₃,W) ≥ (3/2)y(1-y)²` at
  `y = fisherParam p`, for `1/2 < p ≤ 2/3`.  Above `p = 2/3`, Goodman's bound
  `goodman_triangle_bound` is all the catalogue needs.

The parameter `y = fisherParam p = (1 - √(4-6p))/3` is the mass of the small
part of the extremal three-part graphon; `fisherParam_quadratic` is the
identity `p = (1 + 2y - 3y²)/2` that inverts it, and `fisherParam_mem` places
`y` in `[0, 1/3]`.  Arguments that need the extremal profile are cleanest in
the `y` coordinate, where it is the polynomial `(3/2)y(1-y)²`.

Atlas 126 and Atlas 148 (and, through it, Atlas 145) use this bound on their
low-density intervals.
-/

open MeasureTheory

namespace Taeyoung.Methods.TriangleDensity

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Agreement with the graphon vocabulary of `Taeyoung/Fisher/` -/

/-- A bundled graphon is an unbundled one. -/
theorem isGraphon_toFun (W : Graphon Ω μ) :
    Taeyoung.Fisher.IsGraphon (fun x y ↦ W x y) μ :=
  ⟨W.measurable, W.nonneg, W.le_one, W.symm⟩

theorem edgeDensity_bridge (W : Graphon Ω μ) :
    Taeyoung.Fisher.edgeDensity (fun x y ↦ W x y) μ = cliqueDensity 2 W := by
  rw [← integral_degree W]
  rfl

theorem trace_compPow_bridge (W : Graphon Ω μ) :
    Taeyoung.Fisher.trace μ (Taeyoung.Fisher.compPow μ (fun x y ↦ W x y) 2) =
      cliqueDensity 3 W := by
  rw [cliqueDensity_three_eq]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  show (∫ a1, W a0 a1 * (∫ a2, W a1 a2 * W a2 a0 ∂μ) ∂μ)
      = ∫ a1, ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ ∂μ
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  show W a0 a1 * (∫ a2, W a1 a2 * W a2 a0 ∂μ)
      = ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  show W a0 a1 * (W a1 a2 * W a2 a0) = W a0 a1 * W a0 a2 * W a1 a2
  rw [W.symm a2 a0]
  ring

/-! ### The extremal parameter -/

/-- `y = (1 - √(4-6p))/3`: the small part's mass in the extremal three-part
graphon of edge density `p`. -/
noncomputable def fisherParam (p : ℝ) : ℝ := (1 - Real.sqrt (4 - 6 * p)) / 3

/-- The extremal triangle density, in the parameter `y`. -/
noncomputable def fisherProfile (p : ℝ) : ℝ :=
  3 / 2 * fisherParam p * (1 - fisherParam p) ^ 2

/-- `y` lies in `[0, 1/3]` for `1/2 ≤ p ≤ 2/3`. -/
theorem fisherParam_mem {p : ℝ} (hlo : 1 / 2 ≤ p) :
    0 ≤ fisherParam p ∧ fisherParam p ≤ 1 / 3 := by
  constructor
  · rw [fisherParam, le_div_iff₀ (by norm_num : (0:ℝ) < 3), zero_mul, sub_nonneg]
    rcases le_or_gt (4 - 6 * p) 0 with h | h
    · simpa [Real.sqrt_eq_zero_of_nonpos h] using (by norm_num : (0:ℝ) ≤ 1)
    · rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
  · rw [fisherParam, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)]
    have := Real.sqrt_nonneg (4 - 6 * p)
    linarith

/-- The inverse relation `p = (1 + 2y - 3y²)/2`, valid where `4 - 6p ≥ 0`. -/
theorem fisherParam_quadratic {p : ℝ} (hhi : p ≤ 2 / 3) :
    (1 + 2 * fisherParam p - 3 * fisherParam p ^ 2) / 2 = p := by
  have hnn : (0 : ℝ) ≤ 4 - 6 * p := by linarith
  have hsq : Real.sqrt (4 - 6 * p) ^ 2 = 4 - 6 * p := Real.sq_sqrt hnn
  rw [fisherParam]
  field_simp
  nlinarith [hsq]

/-! ### Fisher's bound -/

/-- **Fisher's sharp triangle bound**, `1/2 < p ≤ 2/3`, restated for a bundled
graphon.  The proof is in `Taeyoung/Fisher/`. -/
theorem fisher_triangle_bound (W : Graphon Ω μ)
    (hlo : 1 / 2 < cliqueDensity 2 W) (hhi : cliqueDensity 2 W ≤ 2 / 3) :
    fisherProfile (cliqueDensity 2 W) ≤ cliqueDensity 3 W := by
  have hE := edgeDensity_bridge W
  have h := Taeyoung.Fisher.triangleDensityLowerBound_twoThirds
    (isGraphon_toFun W) (by rw [hE]; exact hlo) (by rw [hE]; exact hhi)
  simp only [hE, trace_compPow_bridge W] at h
  exact h

end Taeyoung.Methods.TriangleDensity
