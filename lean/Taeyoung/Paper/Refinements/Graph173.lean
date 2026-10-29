import Taeyoung.Paper.Refinements.Basic
import Taeyoung.Examples.Graph173
import Taeyoung.Methods.RootedSOS.Refinement.Atlas173.High.Certificate

/-!
# Atlas 173: density range and optimality of `T_k`

`paper.pdf`, Table 1:

* the Goodman-type lower bound holds for `p ≥ 4/5`;
* `T_k` is optimal for every `k ≥ 5`;
* `T_k` is not optimal for `k = 3`.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Taeyoung.Paper.Refinements.Graph173

open Taeyoung Taeyoung.Paper Taeyoung.Methods.PureChordal Taeyoung.Methods.Negative

/-- **Lower bound range** (Table 1): the Goodman-type bound holds
for every graphon of edge density `p ≥ 4/5`.  Rational six-point certificates,
`Methods/RootedSOS/Refinement/Atlas173/`. -/
theorem lowerBoundRange : SatisfiesLowerBoundOn Taeyoung.Examples.Graph173.graph (Set.Ici (4 / 5)) :=
  (SatisfiesLowerBoundOn.Ici_of_Icc Taeyoung.Methods.RootedSOS.Refinement.Atlas173.High.satisfiesLowerBoundOn)

/-- **`T_k` is optimal for every `k ≥ 5`.** -/
theorem turanOptimal (k : ℕ) [NeZero k] (hk : 5 ≤ k) : TuranOptimal Taeyoung.Examples.Graph173.graph k :=
  turanOptimal_of_satisfiesLowerBoundOn lowerBoundRange k
    (mem_Ici_turanDensity (m := 5) (by norm_num) hk (by norm_num))

/-- **`T_3` is not optimal**: `T_5 ⊗ T_6`, of edge density `1 - 1/3`, has a smaller
`H`-density (Section 5.2). -/
theorem not_turanOptimal_three : ¬ TuranOptimal Taeyoung.Examples.Graph173.graph 3 := by
  have h5 : properAssignmentCount Taeyoung.Examples.Graph173.graph 5 = 1980 := by
    rw [Taeyoung.Examples.Graph173.count]; decide
  have h6 : properAssignmentCount Taeyoung.Examples.Graph173.graph 6 = 8640 := by
    rw [Taeyoung.Examples.Graph173.count]; decide
  have h3 : properAssignmentCount Taeyoung.Examples.Graph173.graph 3 = 18 := by
    rw [Taeyoung.Examples.Graph173.count]; decide
  refine not_turanOptimal_of_tensor 3 5 6 (by norm_num) ?_
  rw [h5, h6, h3, Fintype.card_fin]
  norm_num

/-- **The upper bound of (5.1)**: `T_4`, of edge density `3/4`, has
`t(H_173, T_4) = 9/128`. -/
theorem turan4_value :
    edgeDensity (balancedMultipartiteGraphon 4) = 3 / 4 ∧
      homDensity Taeyoung.Examples.Graph173.graph (balancedMultipartiteGraphon 4) = 9 / 128 := by
  refine ⟨by rw [edgeDensity_turan]; norm_num, ?_⟩
  have h4 : properAssignmentCount Taeyoung.Examples.Graph173.graph 4 = 288 := by
    rw [Taeyoung.Examples.Graph173.count]; decide
  rw [homDensity_balancedMultipartite, h4, Fintype.card_fin]
  norm_num

end Taeyoung.Paper.Refinements.Graph173
