import Taeyoung.Paper.Refinements.Basic
import Taeyoung.Examples.Graph197
import Taeyoung.Methods.RootedSOS.Refinement.Atlas197.High.Certificate

/-!
# Atlas 197: density range and optimality of `T_k`

`paper.pdf`, Table 1:

* the Goodman-type lower bound holds for `p ≥ 3/4`;
* `T_k` is optimal for every `k ≥ 4`;
* `T_k` is not optimal for `k = 3`.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Taeyoung.Paper.Refinements.Graph197

open Taeyoung Taeyoung.Paper Taeyoung.Methods.PureChordal Taeyoung.Methods.Negative

/-- **Lower bound range** (Table 1): the Goodman-type bound holds
for every graphon of edge density `p ≥ 3/4`.  Rational six-point certificates,
`Methods/RootedSOS/Refinement/Atlas197/`. -/
theorem lowerBoundRange : SatisfiesLowerBoundOn Taeyoung.Examples.Graph197.graph (Set.Ici (3 / 4)) :=
  (SatisfiesLowerBoundOn.Ici_of_Icc Taeyoung.Methods.RootedSOS.Refinement.Atlas197.High.satisfiesLowerBoundOn)

/-- **`T_k` is optimal for every `k ≥ 4`.** -/
theorem turanOptimal (k : ℕ) [NeZero k] (hk : 4 ≤ k) : TuranOptimal Taeyoung.Examples.Graph197.graph k :=
  turanOptimal_of_satisfiesLowerBoundOn lowerBoundRange k
    (mem_Ici_turanDensity (m := 4) (by norm_num) hk (by norm_num))

/-- **`T_3` is not optimal**: `T_5 ⊗ T_6`, of edge density `1 - 1/3`, has a smaller
`H`-density (Section 5.2). -/
theorem not_turanOptimal_three : ¬ TuranOptimal Taeyoung.Examples.Graph197.graph 3 := by
  have h5 : properAssignmentCount Taeyoung.Examples.Graph197.graph 5 = 1020 := by
    rw [Taeyoung.Examples.Graph197.count]; decide
  have h6 : properAssignmentCount Taeyoung.Examples.Graph197.graph 6 = 5160 := by
    rw [Taeyoung.Examples.Graph197.count]; decide
  have h3 : properAssignmentCount Taeyoung.Examples.Graph197.graph 3 = 6 := by
    rw [Taeyoung.Examples.Graph197.count]; decide
  refine not_turanOptimal_of_tensor 3 5 6 (by norm_num) ?_
  rw [h5, h6, h3, Fintype.card_fin]
  norm_num

end Taeyoung.Paper.Refinements.Graph197
