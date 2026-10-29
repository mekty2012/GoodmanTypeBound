import Taeyoung.Paper.Refinements.Basic
import Taeyoung.Examples.Graph170
import Taeyoung.Paper.Eventual.Main

/-!
# Atlas 170: density range and optimality of `T_k`

`paper.pdf`, Table 1:

* the Goodman-type lower bound holds for `p ≥ 1 - (72·6¹²)⁻¹`;
* `T_k` is optimal for every `k ≥ 72·6¹²`;
* `T_k` is not optimal for `k = 3, 4, 5`.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Taeyoung.Paper.Refinements.Graph170

open Taeyoung Taeyoung.Paper Taeyoung.Methods.PureChordal Taeyoung.Methods.Negative

/-- A triangle on the vertices `0, 2, 4`, so the girth is `3`. -/
theorem girth_eq : Taeyoung.Examples.Graph170.graph.girth = 3 :=
  girth_eq_three_of_adj (a := 0) (b := 2) (c := 4) (by decide) (by decide) (by decide)

/-- **Lower bound range** (Table 1): the Goodman-type bound holds
for every `p ≥ 1 - (72·6¹²)⁻¹`, by the explicit threshold of Theorem 1.6
(1.7), the girth being `3`. -/
theorem lowerBoundRange :
    SatisfiesLowerBoundOn Taeyoung.Examples.Graph170.graph (Set.Ici (1 - 1 / (72 * (6 : ℝ) ^ 12))) := by
  have h := Eventual.satisfiesLowerBoundOn_threshold (H := Taeyoung.Examples.Graph170.graph)
    (by rw [girth_eq]; decide)
  rw [Fintype.card_fin, Nat.cast_ofNat] at h
  exact SatisfiesLowerBoundOn.Ici_of_Ioi h (by norm_num)

/-- **`T_k` is optimal for every `k ≥ 72·6¹²`.** -/
theorem turanOptimal (k : ℕ) [NeZero k] (hk : 72 * 6 ^ 12 ≤ k) : TuranOptimal Taeyoung.Examples.Graph170.graph k :=
  turanOptimal_of_satisfiesLowerBoundOn lowerBoundRange k
    (mem_Ici_turanDensity (by norm_num) hk (by norm_num))

/-- **`T_3` is not optimal**: `T_5 ⊗ T_6`, of edge density `1 - 1/3`, has a smaller
`H`-density (Section 5.2). -/
theorem not_turanOptimal_three : ¬ TuranOptimal Taeyoung.Examples.Graph170.graph 3 := by
  have h5 : properAssignmentCount Taeyoung.Examples.Graph170.graph 5 = 2040 := by
    rw [Taeyoung.Examples.Graph170.count]; decide
  have h6 : properAssignmentCount Taeyoung.Examples.Graph170.graph 6 = 8760 := by
    rw [Taeyoung.Examples.Graph170.count]; decide
  have h3 : properAssignmentCount Taeyoung.Examples.Graph170.graph 3 = 24 := by
    rw [Taeyoung.Examples.Graph170.count]; decide
  refine not_turanOptimal_of_tensor 3 5 6 (by norm_num) ?_
  rw [h5, h6, h3, Fintype.card_fin]
  norm_num

/-- **`T_4` is not optimal**: `T_7 ⊗ T_8`, of edge density `1 - 1/4`, has a smaller
`H`-density (Section 5.2). -/
theorem not_turanOptimal_four : ¬ TuranOptimal Taeyoung.Examples.Graph170.graph 4 := by
  have h7 : properAssignmentCount Taeyoung.Examples.Graph170.graph 7 = 28560 := by
    rw [Taeyoung.Examples.Graph170.count]; decide
  have h8 : properAssignmentCount Taeyoung.Examples.Graph170.graph 8 = 76944 := by
    rw [Taeyoung.Examples.Graph170.count]; decide
  have h4 : properAssignmentCount Taeyoung.Examples.Graph170.graph 4 = 312 := by
    rw [Taeyoung.Examples.Graph170.count]; decide
  refine not_turanOptimal_of_tensor 4 7 8 (by norm_num) ?_
  rw [h7, h8, h4, Fintype.card_fin]
  norm_num

/-- **`T_5` is not optimal**: `T_9 ⊗ T_10`, of edge density `1 - 1/5`, has a smaller
`H`-density (Section 5.2). -/
theorem not_turanOptimal_five : ¬ TuranOptimal Taeyoung.Examples.Graph170.graph 5 := by
  have h9 : properAssignmentCount Taeyoung.Examples.Graph170.graph 9 = 180432 := by
    rw [Taeyoung.Examples.Graph170.count]; decide
  have h10 : properAssignmentCount Taeyoung.Examples.Graph170.graph 10 = 380880 := by
    rw [Taeyoung.Examples.Graph170.count]; decide
  have h5 : properAssignmentCount Taeyoung.Examples.Graph170.graph 5 = 2040 := by
    rw [Taeyoung.Examples.Graph170.count]; decide
  refine not_turanOptimal_of_tensor 5 9 10 (by norm_num) ?_
  rw [h9, h10, h5, Fintype.card_fin]
  norm_num

end Taeyoung.Paper.Refinements.Graph170
