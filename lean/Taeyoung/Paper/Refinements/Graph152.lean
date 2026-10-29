import Taeyoung.Paper.Refinements.Basic
import Taeyoung.Examples.Graph152
import Taeyoung.Methods.RootedSOS.Refinement.Atlas152.Turan3.Certificate
import Taeyoung.Methods.RootedSOS.Refinement.Atlas152.High.Certificate

/-!
# Atlas 152: density range and optimality of `T_k`

`paper.pdf`, Table 1:

* the Goodman-type lower bound holds for `p = 2/3` or `p ≥ 3/4`;
* `T_k` is optimal for every `k ≥ 3`.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Taeyoung.Paper.Refinements.Graph152

open Taeyoung Taeyoung.Paper Taeyoung.Methods.PureChordal Taeyoung.Methods.Negative

/-- **Lower bound range** (Table 1): the Goodman-type bound holds
for every graphon of edge density `p = 2/3` or `p ≥ 3/4`.  Rational six-point certificates,
`Methods/RootedSOS/Refinement/Atlas152/`. -/
theorem lowerBoundRange : SatisfiesLowerBoundOn Taeyoung.Examples.Graph152.graph ({2 / 3} ∪ (Set.Ici (3 / 4))) :=
  SatisfiesLowerBoundOn.union
    Taeyoung.Methods.RootedSOS.Refinement.Atlas152.Turan3.satisfiesLowerBoundOn
    (SatisfiesLowerBoundOn.Ici_of_Icc Taeyoung.Methods.RootedSOS.Refinement.Atlas152.High.satisfiesLowerBoundOn)

/-- **`T_k` is optimal for every `k ≥ 3`.** -/
theorem turanOptimal (k : ℕ) [NeZero k] (hk : 3 ≤ k) : TuranOptimal Taeyoung.Examples.Graph152.graph k := by
  refine turanOptimal_of_satisfiesLowerBoundOn lowerBoundRange k ?_
  rw [Set.mem_union]
  rcases Nat.lt_or_ge k 4 with h | h
  · obtain rfl : k = 3 := by omega
    left
    norm_num
  · right
    exact mem_Ici_turanDensity (m := 4) (by norm_num) h (by norm_num)

end Taeyoung.Paper.Refinements.Graph152
