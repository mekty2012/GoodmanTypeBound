import Taeyoung.Foundation
import Taeyoung.Methods.Negative.Chromatic
import Taeyoung.Methods.Negative.Tensor

/-!
# Atlas 198: counterexample

graph6: `Ep~o`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The witness is `T₅ ⊗ T₆` (`tensorTuran 5 6`), the case `k = 3` of `T_{2k-1} ⊗ T_{2k}`: the
categorical product of two balanced complete multipartite graphons
(`paper.pdf`, Section 5.2).  Its edge density is `p = 2/3`, and

```
t(H,W) = 731/101250 < 2/243 = Φ_H(p),
```

so this graph violates the Goodman-type lower bound.
By `Methods/Negative/Tensor.lean`, `t(H, T_a ⊗ T_b) = P_H(a)·P_H(b)/(ab)^{v(H)}`, here
`P_H(5) = 1020` and `P_H(6) = 5160`.  The chromatic
data comes from the surjective colouring counts, evaluated by `decide +kernel` up to
`j = 5` (`j = 6` is `surjCount_card`); every value of the chromatic polynomial
is then read off `properAssignmentCount_eq_sum`.
-/

open Finset Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Examples.Graph198

open Taeyoung Taeyoung.Methods.Negative

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (0, 5), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 198
  vertexCount := 6
  edgeCount := 11
  chromaticNumber := 3
  graph6 := "Ep~o"
  status := .negative
  formalization := .verified

/-! ### The chromatic data -/

theorem surj_0 : surjCount graph 0 = 0 := by decide +kernel
theorem surj_1 : surjCount graph 1 = 0 := by decide +kernel
theorem surj_2 : surjCount graph 2 = 0 := by decide +kernel
theorem surj_3 : surjCount graph 3 = 6 := by decide +kernel
theorem surj_4 : surjCount graph 4 = 96 := by decide +kernel
theorem surj_5 : surjCount graph 5 = 480 := by decide +kernel

/-- The top count is `6!` for *every* graph on 6 vertices: a
surjection between equal finite cardinalities is a bijection, and an
injective assignment separates every pair. -/
theorem surj_6 : surjCount graph 6 = 720 := by
  rw [surjCount_card graph]
  decide

/-- Every colouring count of this graph, from the surjective counts above. -/
theorem count (k : ℕ) :
    properAssignmentCount graph k = 6 * k.choose 3 + 96 * k.choose 4 + 480 * k.choose 5 + 720 * k.choose 6 := by
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

theorem count_5 : properAssignmentCount graph 5 = 1020 := by
  rw [count]
  decide

theorem count_6 : properAssignmentCount graph 6 = 5160 := by
  rw [count]
  decide

/-! ### The witness -/

/-- Fully checked refutation of the common catalogue proposition. -/
theorem status : ViolatesLowerBound graph := by
  have hp : (1 - 1 / ((5 : ℕ) : ℝ)) * (1 - 1 / ((6 : ℕ) : ℝ)) =
      2 / 3 := by
    norm_num
  refine violatesLowerBound_of_tensor graph chromPoly chromNum 5 6 ?_ ?_
  · rw [admissibleDensity, hp]; norm_num
  · rw [homDensity_tensorTuran, hp,
      chromaticTarget_of_ne_one _
        (by norm_num : (2 : ℝ) / 3 ≠ 1)]
    rw [count_5, count_6]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      surj_0, surj_1, surj_2, surj_3, surj_4, surj_5, surj_6,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

end Taeyoung.Examples.Graph198
