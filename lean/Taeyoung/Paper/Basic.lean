import Taeyoung.Foundation
import Taeyoung.Methods.PureChordal.BalancedMultipartite

/-!
# Shared vocabulary for the statements of `paper.pdf`

`Foundation/Status.lean` fixes the paper's central predicate: `SatisfiesLowerBound H`
is the Goodman-type lower bound `t(H,W) ≥ Φ_H(p)` on the closed interval
`p ≥ p̲_H = 1 - 1/(χ(H)-1)`.  (The paper states it for `p > p̲_H` in (1.2); the closed form
is the stronger statement.)  The paper also speaks about the same inequality on
other density ranges, about its validity "at all sufficiently high densities",
and about optimality of the balanced Turán graphon `T_k` at its own density.
This file names those three notions, with the same quantification over the
chromatic polynomial and over graphons on arbitrary probability spaces as
`SatisfiesLowerBound`.

* `SatisfiesLowerBoundOn H S` — `t(H,W) ≥ Φ_H(p)` whenever `p = t(K₂,W) ∈ S`.
* `EventuallySatisfiesLowerBound H` — there is `p_H < 1` with the bound on
  `(p_H, 1]`.
* `TuranOptimal H k` — `T_k` minimizes `t(H,W)` among graphons of edge density
  `1 - 1/k`.

`T_k` is `balancedMultipartiteGraphon k`, the complete `k`-partite graphon on the
uniform probability space `Fin k` (each point is one part of mass `1/k`).
-/

open MeasureTheory

namespace Taeyoung.Paper

open Taeyoung Taeyoung.Methods.PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Goodman-type inequality `t(H,W) ≥ Φ_H(p)` for every graphon whose edge
density lies in `S`. -/
def SatisfiesLowerBoundOn (H : SimpleGraph V) [DecidableRel H.Adj] (S : Set ℝ) :
    Prop :=
  ∀ P : Polynomial ℝ, IsChromaticPolynomial H P →
    ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      (W : Graphon Ω μ), edgeDensity W ∈ S →
        chromaticTarget (V := V) P (edgeDensity W) ≤ homDensity H W

/-- The Goodman-type inequality holds at all sufficiently high densities: there
is `p_H < 1` such that it holds for every graphon of edge density `p > p_H`. -/
def EventuallySatisfiesLowerBound (H : SimpleGraph V) [DecidableRel H.Adj] :
    Prop :=
  ∃ pH : ℝ, pH < 1 ∧ SatisfiesLowerBoundOn H (Set.Ioi pH)

/-- The balanced complete `k`-partite graphon `T_k` minimizes `t(H,W)` among
graphons of edge density `1 - 1/k`. -/
def TuranOptimal (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ) [NeZero k] :
    Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : Graphon Ω μ), edgeDensity W = 1 - 1 / (k : ℝ) →
      homDensity H (balancedMultipartiteGraphon k) ≤ homDensity H W

lemma SatisfiesLowerBoundOn.mono {H : SimpleGraph V} [DecidableRel H.Adj]
    {S T : Set ℝ} (h : SatisfiesLowerBoundOn H T) (hST : S ⊆ T) :
    SatisfiesLowerBoundOn H S :=
  fun P hP _ _ _ _ W hW ↦ h P hP W (hST hW)

/-- `SatisfiesLowerBound` is the bound on the admissible interval. -/
theorem satisfiesLowerBound_iff_on {H : SimpleGraph V} [DecidableRel H.Adj]
    {r : ℕ} (hr : IsChromaticNumber H r) :
    SatisfiesLowerBound H ↔
      SatisfiesLowerBoundOn H {p | admissibleDensity r p} := by
  constructor
  · intro h P hP Ω _ μ _ W hW
    exact h P r hP hr W hW
  · intro h P s hP hs Ω _ μ _ W hW
    have hsr : s = r := IsChromaticNumber.unique H hs hr
    subst hsr
    exact h P hP W hW

end Taeyoung.Paper
