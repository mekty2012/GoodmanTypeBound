import Goodman.Paper.Refinements.Basic
import Goodman.Examples.Graph143
import Goodman.Methods.RootedSOS.Refinement.Atlas143.High.Certificate
import Goodman.Methods.Negative.TuranThree

/-!
# Atlas 143: density range and optimality of `T_k`

`paper.pdf`, Table 1:

* the Goodman-type lower bound holds for `p ≥ 3/4`;
* `T_k` is optimal for every `k ≥ 4`;
* `T_k` is not optimal for `k = 3`.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Goodman.Paper.Refinements.Graph143

open Goodman Goodman.Paper Goodman.Methods.PureChordal Goodman.Methods.Negative

/-- **Lower bound range** (Table 1): the Goodman-type bound holds
for every graphon of edge density `p ≥ 3/4`.  Rational six-point certificates,
`Methods/RootedSOS/Refinement/Atlas143/`. -/
theorem lowerBoundRange : SatisfiesLowerBoundOn Goodman.Examples.Graph143.graph (Set.Ici (3 / 4)) :=
  (SatisfiesLowerBoundOn.Ici_of_Icc Goodman.Methods.RootedSOS.Refinement.Atlas143.High.satisfiesLowerBoundOn)

/-- **`T_k` is optimal for every `k ≥ 4`.** -/
theorem turanOptimal (k : ℕ) [NeZero k] (hk : 4 ≤ k) : TuranOptimal Goodman.Examples.Graph143.graph k :=
  turanOptimal_of_satisfiesLowerBoundOn lowerBoundRange k
    (mem_Ici_turanDensity (m := 4) (by norm_num) hk (by norm_num))

/-- **`T_3` is not optimal**: the four-part graphon `extraVertexW` of Section 5.2
has edge density `2/3` and a smaller `H`-density than `T_3`. -/
theorem not_turanOptimal_three : ¬ TuranOptimal Goodman.Examples.Graph143.graph 3 := by
  refine not_turanOptimal_of_lt extraVertexW ?_ ?_
  · show cliqueDensity 2 extraVertexW = _
    rw [cliqueDensity_extraVertexW]
    norm_num
  · have h3 : properAssignmentCount Goodman.Examples.Graph143.graph 3 = 24 := by
      rw [Goodman.Examples.Graph143.count]; decide
    rw [Goodman.Examples.Graph143.homDensity_witness, homDensity_balancedMultipartite, h3, Fintype.card_fin]
    norm_num

end Goodman.Paper.Refinements.Graph143
