import Taeyoung.Foundation
import Taeyoung.Methods.Negative.Chromatic
import Taeyoung.Methods.Negative.TuranThree

/-!
# Atlas 141: counterexample

graph6: `EXSw`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The witness is the four-part graphon `extraVertexW`: `T₃` with an extra class `A₁` of mass
`δ = 1/2000`, joined to the three classes `A₂, A₃, A₄` of `T₃` with values `1, 23/50, 23/50`,
and value `ε = 8046/99900025` inside each class of `T₃`
(`paper.pdf`, Section 5.2).  Its edge density is `p = 2/3`, and

```
t(H,W) ≈ 0.03292169509 < 8/243 = Φ_H(p),
```

so this graph violates the Goodman-type lower bound.
Its masses and values are natural numbers over `6000` and `199800050`, so the density is
one kernel sum over `Fin 6 → Fin 4` (`Methods/Negative/WeightedStep.lean`).  The chromatic
data comes from the surjective colouring counts, evaluated by `decide +kernel` up to
`j = 5` (`j = 6` is `surjCount_card`); every value of the chromatic polynomial
is then read off `properAssignmentCount_eq_sum`.
-/

open Finset Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Examples.Graph141

open Taeyoung Taeyoung.Methods.Negative

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (1, 2), (1, 4), (2, 3), (2, 5), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 141
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 3
  graph6 := "EXSw"
  status := .negative
  formalization := .verified

/-! ### The chromatic data -/

theorem surj_0 : surjCount graph 0 = 0 := by decide +kernel
theorem surj_1 : surjCount graph 1 = 0 := by decide +kernel
theorem surj_2 : surjCount graph 2 = 0 := by decide +kernel
theorem surj_3 : surjCount graph 3 = 24 := by decide +kernel
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
    properAssignmentCount graph k = 24 * k.choose 3 + 264 * k.choose 4 + 840 * k.choose 5 + 720 * k.choose 6 := by
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

lemma edgeFinset_eq : graph.edgeFinset = {s(0, 2), s(1, 2), s(1, 4), s(2, 3), s(2, 5), s(3, 4), s(3, 5), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The natural-number numerator of the graph weight. -/
def weightNumerator (z : Fin 6 → Fin 4) : ℕ :=
    extraVertexN (z 0) (z 2) *
    extraVertexN (z 1) (z 2) *
    extraVertexN (z 1) (z 4) *
    extraVertexN (z 2) (z 3) *
    extraVertexN (z 2) (z 5) *
    extraVertexN (z 3) (z 4) *
    extraVertexN (z 3) (z 5) *
    extraVertexN (z 4) (z 5)

lemma graphWeight_eq (z : Fin 6 → Fin 4) :
    graphWeight graph extraVertexW z =
      extraVertexW (z 0) (z 2) *
      extraVertexW (z 1) (z 2) *
      extraVertexW (z 1) (z 4) *
      extraVertexW (z 2) (z 3) *
      extraVertexW (z 2) (z 5) *
      extraVertexW (z 3) (z 4) *
      extraVertexW (z 3) (z 5) *
      extraVertexW (z 4) (z 5) := by
  rw [graphWeight, edgeFinset_eq]
  simp
  ring

lemma graphWeight_nat (z : Fin 6 → Fin 4) :
    graphWeight graph extraVertexW z = (weightNumerator z : ℝ) / (199800050 : ℝ) ^ 8 := by
  rw [graphWeight_eq]
  simp only [extraVertexW_apply, weightNumerator]
  push_cast
  ring

theorem weightSum :
    ∑ z : Fin 6 → Fin 4, (∏ v, extraVertexMass (z v)) * weightNumerator z = 3900806711381038381771689557778609813831410579035298011401592828204967821801844220213264 := by
  decide +kernel

theorem homDensity_witness :
    homDensity graph extraVertexW = 3900806711381038381771689557778609813831410579035298011401592828204967821801844220213264 / (((6000 : ℝ) ^ 6) * (199800050 : ℝ) ^ 8) := by
  rw [homDensity_weighted 4 extraVertexMass 6000 graph extraVertexMass_sum (by norm_num) extraVertexW
    weightNumerator ((199800050 : ℝ) ^ 8) graphWeight_nat, weightSum]
  norm_num

/-- Fully checked refutation of the common catalogue proposition. -/
theorem status : ViolatesLowerBound graph := by
  refine violatesLowerBound_of_weighted graph chromPoly chromNum extraVertexW ?_ ?_
  · rw [cliqueDensity_extraVertexW, admissibleDensity]; norm_num
  · rw [homDensity_witness, cliqueDensity_extraVertexW,
      chromaticTarget_of_ne_one _
        (by norm_num : (2 : ℝ) / 3 ≠ 1)]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      surj_0, surj_1, surj_2, surj_3, surj_4, surj_5, surj_6,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

end Taeyoung.Examples.Graph141
