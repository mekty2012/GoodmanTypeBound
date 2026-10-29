import Taeyoung.Foundation
import Taeyoung.Methods.Negative.Chromatic
import Taeyoung.Methods.Negative.StepGraphon

/-!
# Atlas 129: counterexample

graph6: `EheO`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The witness is the constant graphon `W ≡ 3/4`, the case `k = 4` of `W ≡ 1 - 1/k`
(`paper.pdf`, Section 5.2).  Its edge density is `p = 3/4`, and

```
t(H,W) = 2187/16384 < 69/512 = Φ_H(p),
```

so this graph violates the Goodman-type lower bound.
Its values are natural numbers over `4` on `1` equal parts, so the density is one
kernel sum over `Fin 6 → Fin 1` (`Methods/Negative/StepGraphon.lean`).  The chromatic
data comes from the surjective colouring counts, evaluated by `decide +kernel` up to
`j = 5` (`j = 6` is `surjCount_card`); every value of the chromatic polynomial
is then read off `properAssignmentCount_eq_sum`.
-/

open Finset Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Examples.Graph129

open Taeyoung Taeyoung.Methods.Negative

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (3, 4), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 129
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "EheO"
  status := .negative
  formalization := .verified

/-! ### The chromatic data -/

theorem surj_0 : surjCount graph 0 = 0 := by decide +kernel
theorem surj_1 : surjCount graph 1 = 0 := by decide +kernel
theorem surj_2 : surjCount graph 2 = 0 := by decide +kernel
theorem surj_3 : surjCount graph 3 = 42 := by decide +kernel
theorem surj_4 : surjCount graph 4 = 384 := by decide +kernel
theorem surj_5 : surjCount graph 5 = 960 := by decide +kernel

/-- The top count is `6!` for *every* graph on 6 vertices: a
surjection between equal finite cardinalities is a bijection, and an
injective assignment separates every pair. -/
theorem surj_6 : surjCount graph 6 = 720 := by
  rw [surjCount_card graph]
  decide

/-- Every colouring count of this graph, from the surjective counts above. -/
theorem count (k : ℕ) :
    properAssignmentCount graph k = 42 * k.choose 3 + 384 * k.choose 4 + 960 * k.choose 5 + 720 * k.choose 6 := by
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

/-- The constant graphon `W ≡ 3/4`, as a step graphon on a one-point space. -/
def constantN : Fin 1 → Fin 1 → ℕ := fun _ _ ↦ 3

noncomputable def constantW :
    Graphon (Fin 1) (Taeyoung.Methods.PureChordal.finiteUniformMeasure (Fin 1)) :=
  stepGraphon 1 4 constantN (fun _ _ ↦ rfl) (by decide)

theorem constant_pairSum : ∑ z : Fin 2 → Fin 1, constantN (z 0) (z 1) = 3 := by decide +kernel

theorem cliqueDensity_constantW : cliqueDensity 2 constantW = 3 / 4 := by
  rw [cliqueDensity_two_of_natWeight constantW (fun z ↦ constantN (z 0) (z 1))
    ((4 : ℝ)) (fun z ↦ rfl), constant_pairSum]
  norm_num

lemma edgeFinset_eq : graph.edgeFinset = {s(0, 1), s(0, 4), s(0, 5), s(1, 2), s(2, 3), s(3, 4), s(3, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The natural-number numerator of the graph weight. -/
def weightNumerator (z : Fin 6 → Fin 1) : ℕ :=
    constantN (z 0) (z 1) *
    constantN (z 0) (z 4) *
    constantN (z 0) (z 5) *
    constantN (z 1) (z 2) *
    constantN (z 2) (z 3) *
    constantN (z 3) (z 4) *
    constantN (z 3) (z 5)

lemma graphWeight_eq (z : Fin 6 → Fin 1) :
    graphWeight graph constantW z =
      constantW (z 0) (z 1) *
      constantW (z 0) (z 4) *
      constantW (z 0) (z 5) *
      constantW (z 1) (z 2) *
      constantW (z 2) (z 3) *
      constantW (z 3) (z 4) *
      constantW (z 3) (z 5) := by
  rw [graphWeight, edgeFinset_eq]
  simp
  ring

lemma graphWeight_nat (z : Fin 6 → Fin 1) :
    graphWeight graph constantW z = (weightNumerator z : ℝ) / (4 : ℝ) ^ 7 := by
  rw [graphWeight_eq]
  simp only [constantW, stepGraphon_apply, weightNumerator]
  push_cast
  ring

theorem weightSum : ∑ z : Fin 6 → Fin 1, weightNumerator z = 2187 := by decide +kernel

theorem homDensity_witness :
    homDensity graph constantW = 2187 / (((1 : ℝ) ^ 6) * (4 : ℝ) ^ 7) := by
  rw [homDensity_of_natWeight graph constantW weightNumerator ((4 : ℝ) ^ 7)
    graphWeight_nat, weightSum, Fintype.card_fin]
  norm_num

/-- Fully checked refutation of the common catalogue proposition. -/
theorem status : ViolatesLowerBound graph := by
  refine violatesLowerBound_of_finiteUniform graph chromPoly chromNum constantW ?_ ?_
  · rw [cliqueDensity_constantW, admissibleDensity]; norm_num
  · rw [homDensity_witness, cliqueDensity_constantW,
      chromaticTarget_of_ne_one _
        (by norm_num : (3 : ℝ) / 4 ≠ 1)]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      surj_0, surj_1, surj_2, surj_3, surj_4, surj_5, surj_6,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

end Taeyoung.Examples.Graph129
