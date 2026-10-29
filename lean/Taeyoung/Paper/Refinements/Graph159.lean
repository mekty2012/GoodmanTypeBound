import Taeyoung.Paper.Refinements.Basic
import Taeyoung.Examples.Graph159
import Taeyoung.Methods.RootedSOS.Refinement.Atlas159.High.Certificate
import Taeyoung.Methods.Negative.TuranThree

/-!
# Atlas 159: density range and optimality of `T_k`

`paper.pdf`, Table 1:

* the Goodman-type lower bound holds for `p ≥ 3/4`;
* `T_k` is optimal for every `k ≥ 4`;
* `T_k` is not optimal for `k = 3`.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Taeyoung.Paper.Refinements.Graph159

open Taeyoung Taeyoung.Paper Taeyoung.Methods.PureChordal Taeyoung.Methods.Negative

/-- **Lower bound range** (Table 1): the Goodman-type bound holds
for every graphon of edge density `p ≥ 3/4`.  Rational six-point certificates,
`Methods/RootedSOS/Refinement/Atlas159/`. -/
theorem lowerBoundRange : SatisfiesLowerBoundOn Taeyoung.Examples.Graph159.graph (Set.Ici (3 / 4)) :=
  (SatisfiesLowerBoundOn.Ici_of_Icc Taeyoung.Methods.RootedSOS.Refinement.Atlas159.High.satisfiesLowerBoundOn)

/-- **`T_k` is optimal for every `k ≥ 4`.** -/
theorem turanOptimal (k : ℕ) [NeZero k] (hk : 4 ≤ k) : TuranOptimal Taeyoung.Examples.Graph159.graph k :=
  turanOptimal_of_satisfiesLowerBoundOn lowerBoundRange k
    (mem_Ici_turanDensity (m := 4) (by norm_num) hk (by norm_num))

/-- **`T_3` is not optimal**: the three-part graphon `threePartW` of Section 5.2
has edge density `2/3` and a smaller `H`-density than `T_3`. -/
theorem not_turanOptimal_three : ¬ TuranOptimal Taeyoung.Examples.Graph159.graph 3 := by
  refine not_turanOptimal_of_lt threePartW ?_ ?_
  · show cliqueDensity 2 threePartW = _
    rw [cliqueDensity_threePartW]
    norm_num
  · have h3 : properAssignmentCount Taeyoung.Examples.Graph159.graph 3 = 12 := by
      rw [Taeyoung.Examples.Graph159.count]; decide
    rw [Taeyoung.Examples.Graph159.homDensity_witness, homDensity_balancedMultipartite, h3, Fintype.card_fin]
    norm_num

end Taeyoung.Paper.Refinements.Graph159
