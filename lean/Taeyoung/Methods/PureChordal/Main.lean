import Taeyoung.Methods.PureChordal.ChromaticFactorization
import Taeyoung.Foundation.Status

/-!
# The pure-chordal graphon inequalities

A chordal graph all of whose maximal cliques have size `r ≥ 3` satisfies the
Goodman-type lower bound (`pureChordal_satisfiesLowerBound`, Theorem 1.1
of `paper.pdf`).  `PureCliqueTreeDecomp.satisfiesLowerBound` derives it from a
clique-tree certificate.
-/

namespace Taeyoung.Methods.PureChordal

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} {r : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- A pure clique-tree certificate proves the common catalogue proposition.

This is the bridge from the method-specific theorem to the shared foundation.
It handles `p = 1` separately, so no division by zero is hidden in the use of
the factored chromatic polynomial. -/
theorem PureCliqueTreeDecomp.satisfiesLowerBound
    [DecidableRel H.Adj]
    (D : PureCliqueTreeDecomp H r m)
    (hr : 3 ≤ r) :
    Taeyoung.SatisfiesLowerBound H := by
  intro P s hP hs Ω instMeas μ instProb W hp
  have hpoly : P = D.chromaticPolynomial :=
    Taeyoung.IsChromaticPolynomial.unique (H := H) hP D.isChromaticPolynomial
  have hchrom : s = r :=
    Taeyoung.IsChromaticNumber.unique (H := H) hs D.isChromaticNumber
  subst P
  subst s
  change 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W at hp
  change chromaticTarget D.chromaticPolynomial (cliqueDensity 2 W) ≤
    homDensity H W
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    have hbound := D.certificateBound_le_homDensity W hr hp
    have hcert : D.certificateBound 1 = 1 := by
      simp [PureCliqueTreeDecomp.certificateBound,
        PureCliqueTreeDecomp.cliquePolyTail, cliquePoly]
    rw [hone, hcert] at hbound
    exact hbound
  · rw [chromaticTarget_of_ne_one D.chromaticPolynomial hone]
    rw [← D.certificateBound_eq_eval_chromaticPolynomial hone]
    exact D.certificateBound_le_homDensity W hr hp

/-- Catalogue-facing form of the pure-chordal theorem. -/
theorem pureChordal_satisfiesLowerBound
    [DecidableRel H.Adj]
    (hchordal : IsChordal H)
    (hpure : HasPureMaximalCliques H r)
    (hr : 3 ≤ r) :
    Taeyoung.SatisfiesLowerBound H :=
  (hchordal.pureDecomp hpure).satisfiesLowerBound hr

end Taeyoung.Methods.PureChordal
