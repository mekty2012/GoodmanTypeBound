import Taeyoung.Foundation
import Taeyoung.Methods.Negative.Chromatic
import Taeyoung.Methods.Negative.TuranThree

/-!
# Atlas 159: counterexample

graph6: `EZSw`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The witness is the three-part graphon `threePartW`, with classes of masses `13/40, 7/20, 13/40`,
value `557/14700` inside the middle class, `49/50` between the outer classes, `1` between
the middle class and the outer ones, and `0` inside the outer classes
(`paper.pdf`, Section 5.2).  Its edge density is `p = 2/3`, and

```
t(H,W) ≈ 0.01645916157 < 4/243 = Φ_H(p),
```

so this graph violates the Goodman-type lower bound.
Its masses and values are natural numbers over `40` and `14700`, so the density is
one kernel sum over `Fin 6 → Fin 3` (`Methods/Negative/WeightedStep.lean`).  The chromatic
data comes from the surjective colouring counts, evaluated by `decide +kernel` up to
`j = 5` (`j = 6` is `surjCount_card`); every value of the chromatic polynomial
is then read off `properAssignmentCount_eq_sum`.
-/

open Finset Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Examples.Graph159

open Taeyoung Taeyoung.Methods.Negative

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 5), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 159
  vertexCount := 6
  edgeCount := 9
  chromaticNumber := 3
  graph6 := "EZSw"
  status := .negative
  formalization := .verified

/-! ### The chromatic data -/

theorem surj_0 : surjCount graph 0 = 0 := by decide +kernel
theorem surj_1 : surjCount graph 1 = 0 := by decide +kernel
theorem surj_2 : surjCount graph 2 = 0 := by decide +kernel
theorem surj_3 : surjCount graph 3 = 12 := by decide +kernel
theorem surj_4 : surjCount graph 4 = 168 := by decide +kernel
theorem surj_5 : surjCount graph 5 = 720 := by decide +kernel

/-- The top count is `6!` for *every* graph on 6 vertices: a
surjection between equal finite cardinalities is a bijection, and an
injective assignment separates every pair. -/
theorem surj_6 : surjCount graph 6 = 720 := by
  rw [surjCount_card graph]
  decide

/-- Every colouring count of this graph, from the surjective counts above. -/
theorem count (k : ℕ) :
    properAssignmentCount graph k = 12 * k.choose 3 + 168 * k.choose 4 + 720 * k.choose 5 + 720 * k.choose 6 := by
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

/-! ### The witness -/

lemma edgeFinset_eq : graph.edgeFinset = {s(0, 2), s(1, 2), s(1, 3), s(1, 4), s(2, 3), s(2, 5), s(3, 4), s(3, 5), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The natural-number numerator of the graph weight. -/
def weightNumerator (z : Fin 6 → Fin 3) : ℕ :=
    threePartN (z 0) (z 2) *
    threePartN (z 1) (z 2) *
    threePartN (z 1) (z 3) *
    threePartN (z 1) (z 4) *
    threePartN (z 2) (z 3) *
    threePartN (z 2) (z 5) *
    threePartN (z 3) (z 4) *
    threePartN (z 3) (z 5) *
    threePartN (z 4) (z 5)

lemma graphWeight_eq (z : Fin 6 → Fin 3) :
    graphWeight graph threePartW z =
      threePartW (z 0) (z 2) *
      threePartW (z 1) (z 2) *
      threePartW (z 1) (z 3) *
      threePartW (z 1) (z 4) *
      threePartW (z 2) (z 3) *
      threePartW (z 2) (z 5) *
      threePartW (z 3) (z 4) *
      threePartW (z 3) (z 5) *
      threePartW (z 4) (z 5) := by
  rw [graphWeight, edgeFinset_eq]
  simp
  ring

lemma graphWeight_nat (z : Fin 6 → Fin 3) :
    graphWeight graph threePartW z = (weightNumerator z : ℝ) / (14700 : ℝ) ^ 9 := by
  rw [graphWeight_eq]
  simp only [threePartW_apply, weightNumerator]
  push_cast
  ring

theorem weightSum :
    ∑ z : Fin 6 → Fin 3, (∏ v, threePartMass (z v)) * weightNumerator z = 2160845266797498337969107274037630702333452352 := by
  decide +kernel

theorem homDensity_witness :
    homDensity graph threePartW = 2160845266797498337969107274037630702333452352 / (((40 : ℝ) ^ 6) * (14700 : ℝ) ^ 9) := by
  rw [homDensity_weighted 3 threePartMass 40 graph threePartMass_sum (by norm_num) threePartW
    weightNumerator ((14700 : ℝ) ^ 9) graphWeight_nat, weightSum]
  norm_num

/-- Fully checked refutation of the common catalogue proposition. -/
theorem status : ViolatesLowerBound graph := by
  refine violatesLowerBound_of_weighted graph chromPoly chromNum threePartW ?_ ?_
  · rw [cliqueDensity_threePartW, admissibleDensity]; norm_num
  · rw [homDensity_witness, cliqueDensity_threePartW,
      chromaticTarget_of_ne_one _
        (by norm_num : (2 : ℝ) / 3 ≠ 1)]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      surj_0, surj_1, surj_2, surj_3, surj_4, surj_5, surj_6,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

end Taeyoung.Examples.Graph159
