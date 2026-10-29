import Taeyoung.Examples.Graph159
import Taeyoung.Methods.RootedSOS.Refinement.Atlas159.Target
import Taeyoung.Foundation.GraphMap

/-! Atlas 159: the certificates' target polynomial is `Φ_H`, and the graph on six
sample points used by the induced expansion is the catalogue row
`Taeyoung.Examples.Graph159.graph`. -/

open Finset Polynomial MeasureTheory

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas159

open Taeyoung

set_option maxHeartbeats 4000000 in
/-- **`Φ_H` is the explicit target polynomial.** -/
theorem chromaticTarget_eq {P : Polynomial ℝ}
    (hP : IsChromaticPolynomial Taeyoung.Examples.Graph159.graph P) (p : ℝ) :
    chromaticTarget (V := Fin 6) P p = target159 p := by
  have hPeq := IsChromaticPolynomial.unique (H := Taeyoung.Examples.Graph159.graph) hP Taeyoung.Examples.Graph159.chromPoly
  subst hPeq
  by_cases hone : p = 1
  · subst hone
    rw [chromaticTarget_at_one]
    norm_num [target159]
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hone)
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero, Taeyoung.Examples.Graph159.surj_0, Taeyoung.Examples.Graph159.surj_1, Taeyoung.Examples.Graph159.surj_2, Taeyoung.Examples.Graph159.surj_3, Taeyoung.Examples.Graph159.surj_4, Taeyoung.Examples.Graph159.surj_5, Taeyoung.Examples.Graph159.surj_6, target159,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    field_simp
    ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem density_eq_of_graph_eq {n : ℕ}
    (H K : SimpleGraph (Fin n)) [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (W : Graphon Ω μ) (h : H = K) : homDensity H W = homDensity K W := by
  subst K
  have hd : dH = dK := Subsingleton.elim _ _
  subst dK
  rfl

theorem homDensity_target_graph (W : Graphon Ω μ) :
    homDensity Target.graph W = homDensity Taeyoung.Examples.Graph159.graph W :=
  density_eq_of_graph_eq _ _ W rfl

end Taeyoung.Methods.RootedSOS.Refinement.Atlas159
