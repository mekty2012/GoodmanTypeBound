import Taeyoung.Fisher.FiniteGraphon
import Taeyoung.Fisher.GraphonSampling
import Taeyoung.Fisher.Interface
import Taeyoung.Fisher.GraphonScaling

/-!
# From finite graphs to graphons

Fisher's theorem is a statement about finite graphs; this file transfers it to
graphons.  The finite density form gives, for every finite graph on the density
band, `q ≥ p - 4/9 - (4/9)(1 - 3p/2)^{3/2}`.  For a graphon `W`, the edge
density `edgeDensity W μ = t(K₂, W)` and the triangle density
`trace μ (compPow μ W 2) = t(K₃, W)` are limits along the finite graphs of
`GraphonSampling` (after scaling `W` into the interior of the band with
`GraphonScaling`), and the bound passes to the limit by continuity.

The result is `triangleDensityLowerBound_twoThirds : TriangleDensityLowerBoundUpTo (2/3)`.
-/

open MeasureTheory
open scoped Topology

namespace Taeyoung.Fisher

universe u

/-- Fisher's lower-envelope function in edge-density coordinates. -/
noncomputable def fisherCurve (p : ℝ) : ℝ :=
  p - 4 / 9 - (4 / 9) * (1 - 3 * p / 2) ^ ((3 : ℝ) / 2)

theorem continuous_fisherCurve : Continuous fisherCurve := by
  unfold fisherCurve
  have hbase : Continuous (fun p : ℝ => 1 - 3 * p / 2) := by fun_prop
  have hpow : Continuous
      (fun p : ℝ => (1 - 3 * p / 2) ^ ((3 : ℝ) / 2)) :=
    hbase.rpow_const (fun _ => Or.inr (by norm_num))
  exact (continuous_id.sub continuous_const).sub (continuous_const.mul hpow)

/-- The graphon triangle density equals `t(K₃, W)`; `edgeDensity` is `t(K₂, W)`.
The algebraic identity `(3/2)·c·(1-c)^2 = p - 4/9 - (4/9)(1-3p/2)^{3/2}` for
`c = (1 - √(4-6p))/3` (with `u = √(1-3p/2)`, `c = (1-2u)/3`) connects the two
statements. -/
theorem fisher_density_param_eq (p : ℝ) (hp : 1 / 2 ≤ p) (hpu : p ≤ 2 / 3) :
    let c := (1 - Real.sqrt (4 - 6 * p)) / 3
    (3 / 2) * c * (1 - c) ^ 2
      = p - 4 / 9 - (4 / 9) * (1 - 3 * p / 2) ^ ((3 : ℝ) / 2) := by
  have harg : 0 ≤ 4 - 6 * p := by nlinarith
  have ha : 0 ≤ 1 - 3 * p / 2 := by nlinarith
  have hs0 : 0 ≤ Real.sqrt (4 - 6 * p) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p := Real.sq_sqrt harg
  have hsa0 : 0 ≤ Real.sqrt (1 - 3 * p / 2) := Real.sqrt_nonneg _
  have hsa2 : (Real.sqrt (1 - 3 * p / 2)) ^ 2 = 1 - 3 * p / 2 :=
    Real.sq_sqrt ha
  have hsqrt :
      Real.sqrt (1 - 3 * p / 2) = Real.sqrt (4 - 6 * p) / 2 := by
    have hhalf0 : 0 ≤ Real.sqrt (4 - 6 * p) / 2 := by positivity
    nlinarith
  have hrpow :
      (1 - 3 * p / 2) ^ ((3 : ℝ) / 2) =
        (Real.sqrt (4 - 6 * p) / 2) ^ 3 := by
    rw [Real.rpow_div_two_eq_sqrt (3 : ℝ) ha]
    norm_num
    rw [hsqrt]
  dsimp
  rw [hrpow]
  ring_nf
  have hs2' : (Real.sqrt (4 - p * 6)) ^ 2 = 4 - p * 6 := by
    convert hs2 using 1 <;> ring
  nlinarith [hs2']

/-- The core finite-transfer statement on the open density band.  Strict
margins are exactly what finite sampling/rounding needs: sufficiently accurate
finite approximants remain in Fisher's finite density band. -/
private theorem fisher_density_form_graphon_interior
    {Ω' : Type u} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {W' : Ω' → Ω' → ℝ}
    (hW' : IsGraphon W' μ')
    (hlo : 1 / 2 < edgeDensity W' μ')
    (hhi : edgeDensity W' μ' < 2 / 3) :
    fisherCurve (edgeDensity W' μ') ≤
      trace μ' (compPow μ' W' 2) := by
  -- Approximate by weighted finite step kernels, clear denominators by
  -- blow-up, and round the finitely many edge weights.  The strict margins
  -- keep sufficiently accurate finite graphs in Fisher's density band.
  obtain ⟨G, hedge, htriangle⟩ :=
    exists_finiteGraph_density_approximants hW'
  have hloEventually : ∀ᶠ n in Filter.atTop,
      1 / 2 ≤ (G n).edgeDensity := by
    exact (hedge.eventually (Ioi_mem_nhds hlo)).mono fun _ hn => hn.le
  have hhiEventually : ∀ᶠ n in Filter.atTop,
      (G n).edgeDensity ≤ 2 / 3 := by
    exact (hedge.eventually (Iio_mem_nhds hhi)).mono fun _ hn => hn.le
  have hineq : ∀ᶠ n in Filter.atTop,
      fisherCurve (G n).edgeDensity ≤ (G n).triangleDensity := by
    filter_upwards [hloEventually, hhiEventually] with n hnlo hnhi
    simpa [fisherCurve] using
      (FiniteGraphApprox.fisher_density_form (G n) hnlo hnhi)
  exact le_of_tendsto_of_tendsto
    (continuous_fisherCurve.continuousAt.tendsto.comp hedge)
    htriangle hineq

/-- Transfer from the open band to its closed upper endpoint by scaling the
kernel toward zero. -/
theorem fisher_density_form_graphon_strict
    {Ω' : Type u} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {W' : Ω' → Ω' → ℝ}
    (hW' : IsGraphon W' μ')
    (hlo : 1 / 2 < edgeDensity W' μ')
    (hhi : edgeDensity W' μ' ≤ 2 / 3) :
    edgeDensity W' μ' - 4 / 9 -
        (4 / 9) * (1 - 3 * edgeDensity W' μ' / 2) ^ ((3 : ℝ) / 2) ≤
      trace μ' (compPow μ' W' 2) := by
  obtain ⟨A, hA, hconv, hband⟩ :=
    exists_interior_scaled_graphons hW' hlo hhi
  change fisherCurve (edgeDensity W' μ') ≤ trace μ' (compPow μ' W' 2)
  exact density_inequality_of_kernelL1_approx hW' A hA hconv fisherCurve
    continuous_fisherCurve.continuousAt
    (fun n => fisher_density_form_graphon_interior (hA n)
      (hband n).1 (hband n).2)

/-- **Fisher's bound for graphons**, on the full band `1/2 < p ≤ 2/3`. -/
theorem triangleDensityLowerBound_twoThirds :
    TriangleDensityLowerBoundUpTo.{u} (2 / 3) := by
  intro Omega' _ mu' _ W' hW' hgt hle
  dsimp
  rw [fisher_density_param_eq (edgeDensity W' mu') hgt.le hle]
  exact fisher_density_form_graphon_strict hW' hgt hle

end Taeyoung.Fisher
