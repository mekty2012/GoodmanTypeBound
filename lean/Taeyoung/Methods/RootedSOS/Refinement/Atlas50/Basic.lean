import Taeyoung.Examples.Graph050
import Taeyoung.Methods.RootedSOS.Refinement.Atlas50.Target
import Taeyoung.Foundation.GraphMap

/-! Atlas 50: the certificates' target polynomial is `Φ_H`, and the graph on six
sample points used by the induced expansion is the catalogue row
`Taeyoung.Examples.Graph050.graph` with one isolated vertex appended. -/

open Finset Polynomial MeasureTheory

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas50

open Taeyoung

set_option maxHeartbeats 4000000 in
/-- **`Φ_H` is the explicit target polynomial.** -/
theorem chromaticTarget_eq {P : Polynomial ℝ}
    (hP : IsChromaticPolynomial Taeyoung.Examples.Graph050.graph P) (p : ℝ) :
    chromaticTarget (V := Fin 5) P p = target50 p := by
  have hPeq := IsChromaticPolynomial.unique (H := Taeyoung.Examples.Graph050.graph) hP Taeyoung.Examples.Graph050.chromPoly
  subst hPeq
  by_cases hone : p = 1
  · subst hone
    rw [chromaticTarget_at_one]
    norm_num [target50]
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hone)
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero, Taeyoung.Examples.Graph050.surj_0, Taeyoung.Examples.Graph050.surj_1, Taeyoung.Examples.Graph050.surj_2, Taeyoung.Examples.Graph050.surj_3, Taeyoung.Examples.Graph050.surj_4, Taeyoung.Examples.Graph050.surj_5, target50,
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

private theorem target_graph_eq :
    Target.graph = (Taeyoung.Examples.Graph050.graph).map (Fin.castAdd 1) := by
  ext u v
  revert u v
  decide +kernel

theorem homDensity_target_graph (W : Graphon Ω μ) :
    homDensity Target.graph W = homDensity Taeyoung.Examples.Graph050.graph W := by
  classical
  rw [density_eq_of_graph_eq _ _ W target_graph_eq]
  exact homDensity_map_castAdd _ 1 W

end Taeyoung.Methods.RootedSOS.Refinement.Atlas50
