import Taeyoung.Foundation
import Taeyoung.Methods.Negative.Chromatic
import Taeyoung.Methods.Negative.Atlas152

/-!
# Atlas 152: counterexample

graph6: `EhNG`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The witness is the five-part graphon `W152 = W_ε` at `ε = 1/3000`, on the classes
`A₁, A₂, B, S₁, S₂` of masses `(1/2-ε)·624/625, (1/2-ε)/625, 1/2, ε/10, 9ε/10`, with value
`1/16` between `B` and `S₁`
(`paper.pdf`, Section 5.2).  Its edge density is `p = 18750093281/37500000000`, and

```
t(H,W) ≈ 3.085993723e-12 < 3.093826934e-12 ≈ Φ_H(p),
```

so this graph violates the Goodman-type lower bound.
Its masses and values are natural numbers over `3750000` and `16`, so the density is
one kernel sum over `Fin 6 → Fin 5` (`Methods/Negative/WeightedStep.lean`).  The chromatic
data comes from the surjective colouring counts, evaluated by `decide +kernel` up to
`j = 5` (`j = 6` is `surjCount_card`); every value of the chromatic polynomial
is then read off `properAssignmentCount_eq_sum`.
-/

open Finset Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Examples.Graph152

open Taeyoung Taeyoung.Methods.Negative

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 5), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 152
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 3
  graph6 := "EhNG"
  status := .negative
  formalization := .verified

/-! ### The chromatic data -/

theorem surj_0 : surjCount graph 0 = 0 := by decide +kernel
theorem surj_1 : surjCount graph 1 = 0 := by decide +kernel
theorem surj_2 : surjCount graph 2 = 0 := by decide +kernel
theorem surj_3 : surjCount graph 3 = 18 := by decide +kernel
theorem surj_4 : surjCount graph 4 = 264 := by decide +kernel
theorem surj_5 : surjCount graph 5 = 840 := by decide +kernel

/-- The top count is `6!` for *every* graph on 6 vertices: a
surjection between equal finite cardinalities is a bijection, and an
injective assignment separates every pair. -/
theorem surj_6 : surjCount graph 6 = 720 := by
  rw [surjCount_card graph]
  decide

/-- Every colouring count of this graph, from the surjective counts above. -/
theorem count (k : ℕ) :
    properAssignmentCount graph k = 18 * k.choose 3 + 264 * k.choose 4 + 840 * k.choose 5 + 720 * k.choose 6 := by
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

lemma edgeFinset_eq : graph.edgeFinset = {s(0, 1), s(0, 5), s(1, 2), s(1, 5), s(2, 3), s(2, 4), s(3, 4), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The natural-number numerator of the graph weight. -/
def weightNumerator (z : Fin 6 → Fin 5) : ℕ :=
    N152 (z 0) (z 1) *
    N152 (z 0) (z 5) *
    N152 (z 1) (z 2) *
    N152 (z 1) (z 5) *
    N152 (z 2) (z 3) *
    N152 (z 2) (z 4) *
    N152 (z 3) (z 4) *
    N152 (z 4) (z 5)

lemma graphWeight_eq (z : Fin 6 → Fin 5) :
    graphWeight graph W152 z =
      W152 (z 0) (z 1) *
      W152 (z 0) (z 5) *
      W152 (z 1) (z 2) *
      W152 (z 1) (z 5) *
      W152 (z 2) (z 3) *
      W152 (z 2) (z 4) *
      W152 (z 3) (z 4) *
      W152 (z 4) (z 5) := by
  rw [graphWeight, edgeFinset_eq]
  simp
  ring

lemma graphWeight_nat (z : Fin 6 → Fin 5) :
    graphWeight graph W152 z = (weightNumerator z : ℝ) / (16 : ℝ) ^ 8 := by
  rw [graphWeight_eq]
  simp only [W152_apply, weightNumerator]
  push_cast
  ring

theorem weightSum :
    ∑ z : Fin 6 → Fin 5, (∏ v, w152 (z v)) * weightNumerator z = 36858911528492236800000000000000000000 := by
  decide +kernel

theorem homDensity_witness :
    homDensity graph W152 = 36858911528492236800000000000000000000 / (((3750000 : ℝ) ^ 6) * (16 : ℝ) ^ 8) := by
  rw [homDensity_weighted 5 w152 3750000 graph w152_sum (by norm_num) W152
    weightNumerator ((16 : ℝ) ^ 8) graphWeight_nat, weightSum]
  norm_num

/-- Fully checked refutation of the common catalogue proposition. -/
theorem status : ViolatesLowerBound graph := by
  refine violatesLowerBound_of_weighted graph chromPoly chromNum W152 ?_ ?_
  · rw [cliqueDensity_152, admissibleDensity]; norm_num
  · rw [homDensity_witness, cliqueDensity_152,
      chromaticTarget_of_ne_one _
        (by norm_num : (18750093281 : ℝ) / 37500000000 ≠ 1)]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      surj_0, surj_1, surj_2, surj_3, surj_4, surj_5, surj_6,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

end Taeyoung.Examples.Graph152
