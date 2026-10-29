import Taeyoung.Fisher.Kernel

/-!
# The graphon form of Fisher's bound

`TriangleDensityLowerBoundUpTo ρ` says: for every graphon `W` with edge density
`p = edgeDensity W μ` in `(1/2, ρ]`, writing `c := (1 - √(4 - 6p)) / 3`, the
triangle density obeys `(3/2)·c·(1-c)^2 ≤ t(K₃, W) = trace μ (compPow μ W 2)`.
`GraphonBridge` proves it for `ρ = 2/3`.

With `u := √(1 - 3p/2)` one has `c = (1-2u)/3` and `(3/2)·c·(1-c)^2 =
p - 4/9 - (4/9)·u^3`, which is Fisher's density form
`q ≥ p - 4/9 - (4/9)(1 - 3p/2)^{3/2}`.
-/

open MeasureTheory

namespace Taeyoung.Fisher

universe u

/-- Fisher's triangle-density lower bound for graphons up to an edge-density
cutoff `rho`: `(3/2)·c·(1-c)^2 ≤ t(K₃, W)` with `c = (1 - √(4 - 6p))/3`,
whenever `1/2 < p ≤ rho`.  This is the extremal profile of the clique density
theorem (Razborov, Reiher) on that band. -/
def TriangleDensityLowerBoundUpTo (rho : Real) : Prop :=
  forall {Omega' : Type u} [MeasurableSpace Omega']
    {mu' : Measure Omega'} [IsProbabilityMeasure mu']
    {W' : Omega' -> Omega' -> Real},
    IsGraphon W' mu' ->
    1 / 2 < edgeDensity W' mu' ->
    edgeDensity W' mu' <= rho ->
    let c := (1 - Real.sqrt (4 - 6 * edgeDensity W' mu')) / 3
    (3 / 2) * c * (1 - c) ^ 2 <= trace mu' (compPow mu' W' 2)

end Taeyoung.Fisher
