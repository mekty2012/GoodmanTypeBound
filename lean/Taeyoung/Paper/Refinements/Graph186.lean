import Taeyoung.Paper.Refinements.Basic
import Taeyoung.Examples.Graph186
import Taeyoung.Methods.RootedSOS.Refinement.Atlas186.Turan4.Certificate
import Taeyoung.Methods.RootedSOS.Refinement.Atlas186.High.Certificate

/-!
# Atlas 186: density range and optimality of `T_k`

`paper.pdf`, Table 1:

* the Goodman-type lower bound holds for `p = 3/4` or `p ≥ 4/5`;
* `T_k` is optimal for every `k ≥ 4`;
* `T_k` is not optimal for `k = 3`.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Taeyoung.Paper.Refinements.Graph186

open Taeyoung Taeyoung.Paper Taeyoung.Methods.PureChordal Taeyoung.Methods.Negative

/-- **Lower bound range** (Table 1): the Goodman-type bound holds
for every graphon of edge density `p = 3/4` or `p ≥ 4/5`.  Rational six-point certificates,
`Methods/RootedSOS/Refinement/Atlas186/`. -/
theorem lowerBoundRange : SatisfiesLowerBoundOn Taeyoung.Examples.Graph186.graph ({3 / 4} ∪ (Set.Ici (4 / 5))) :=
  SatisfiesLowerBoundOn.union
    Taeyoung.Methods.RootedSOS.Refinement.Atlas186.Turan4.satisfiesLowerBoundOn
    (SatisfiesLowerBoundOn.Ici_of_Icc Taeyoung.Methods.RootedSOS.Refinement.Atlas186.High.satisfiesLowerBoundOn)

/-- **`T_k` is optimal for every `k ≥ 4`.** -/
theorem turanOptimal (k : ℕ) [NeZero k] (hk : 4 ≤ k) : TuranOptimal Taeyoung.Examples.Graph186.graph k := by
  refine turanOptimal_of_satisfiesLowerBoundOn lowerBoundRange k ?_
  rw [Set.mem_union]
  rcases Nat.lt_or_ge k 5 with h | h
  · obtain rfl : k = 4 := by omega
    left
    norm_num
  · right
    exact mem_Ici_turanDensity (m := 5) (by norm_num) h (by norm_num)

/-- **`T_3` is not optimal**: `T_5 ⊗ T_6`, of edge density `1 - 1/3`, has a smaller
`H`-density (Section 5.2). -/
theorem not_turanOptimal_three : ¬ TuranOptimal Taeyoung.Examples.Graph186.graph 3 := by
  have h5 : properAssignmentCount Taeyoung.Examples.Graph186.graph 5 = 1440 := by
    rw [Taeyoung.Examples.Graph186.count]; decide
  have h6 : properAssignmentCount Taeyoung.Examples.Graph186.graph 6 = 6720 := by
    rw [Taeyoung.Examples.Graph186.count]; decide
  have h3 : properAssignmentCount Taeyoung.Examples.Graph186.graph 3 = 12 := by
    rw [Taeyoung.Examples.Graph186.count]; decide
  refine not_turanOptimal_of_tensor 3 5 6 (by norm_num) ?_
  rw [h5, h6, h3, Fintype.card_fin]
  norm_num

end Taeyoung.Paper.Refinements.Graph186
