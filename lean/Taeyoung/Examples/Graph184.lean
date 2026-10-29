import Taeyoung.Foundation
import Taeyoung.Methods.Negative.Chromatic
import Taeyoung.Methods.Negative.Tensor

/-!
# Atlas 184: counterexample

graph6: `Elfo`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The witness is `T_4 ⊗ T_4` (`tensorTuran 4 4`), the categorical product of two
balanced complete multipartite graphons
(`paper.pdf`, Section 5.2).  Its edge density is `p = 9/16`, and

```
t(H,W) = 81/65536 < 351/262144 = Φ_H(p),
```

so this graph violates the Goodman-type lower bound.
By `Methods/Negative/Tensor.lean`, `t(H, T_a ⊗ T_b) = P_H(a)·P_H(b)/(ab)^{v(H)}`, here
`P_H(4) = 144` and `P_H(4) = 144`.  The chromatic
data comes from the surjective colouring counts, evaluated by `decide +kernel` up to
`j = 5` (`j = 6` is `surjCount_card`); every value of the chromatic polynomial
is then read off `properAssignmentCount_eq_sum`.
-/

open Finset Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Examples.Graph184

open Taeyoung Taeyoung.Methods.Negative

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 184
  vertexCount := 6
  edgeCount := 10
  chromaticNumber := 3
  graph6 := "Elfo"
  status := .negative
  formalization := .verified

/-! ### The chromatic data -/

theorem surj_0 : surjCount graph 0 = 0 := by decide +kernel
theorem surj_1 : surjCount graph 1 = 0 := by decide +kernel
theorem surj_2 : surjCount graph 2 = 0 := by decide +kernel
theorem surj_3 : surjCount graph 3 = 6 := by decide +kernel
theorem surj_4 : surjCount graph 4 = 120 := by decide +kernel
theorem surj_5 : surjCount graph 5 = 600 := by decide +kernel

/-- The top count is `6!` for *every* graph on 6 vertices: a
surjection between equal finite cardinalities is a bijection, and an
injective assignment separates every pair. -/
theorem surj_6 : surjCount graph 6 = 720 := by
  rw [surjCount_card graph]
  decide

/-- Every colouring count of this graph, from the surjective counts above. -/
theorem count (k : ℕ) :
    properAssignmentCount graph k = 6 * k.choose 3 + 120 * k.choose 4 + 600 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    surj_0, surj_1, surj_2, surj_3, surj_4, surj_5, surj_6]
  ring

theorem chromNum : IsChromaticNumber graph 3 where
  positive := by rw [count]; decide
  zero_below k hk := by
    rw [count]
    interval_cases k <;> decide

theorem chromPoly : IsChromaticPolynomial graph
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph j : ℝ) / (j).factorial) * ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph

theorem count_4 : properAssignmentCount graph 4 = 144 := by
  rw [count]
  decide

/-! ### The witness -/

/-- Fully checked refutation of the common catalogue proposition. -/
theorem status : ViolatesLowerBound graph := by
  have hp : (1 - 1 / ((4 : ℕ) : ℝ)) * (1 - 1 / ((4 : ℕ) : ℝ)) =
      9 / 16 := by
    norm_num
  refine violatesLowerBound_of_tensor graph chromPoly chromNum 4 4 ?_ ?_
  · rw [admissibleDensity, hp]; norm_num
  · rw [homDensity_tensorTuran, hp,
      chromaticTarget_of_ne_one _
        (by norm_num : (9 : ℝ) / 16 ≠ 1)]
    rw [count_4]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      surj_0, surj_1, surj_2, surj_3, surj_4, surj_5, surj_6,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

end Taeyoung.Examples.Graph184
