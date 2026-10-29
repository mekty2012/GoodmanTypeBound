import Taeyoung.Paper.Refinements.Basic
import Taeyoung.Examples.Graph206
import Taeyoung.Methods.RootedSOS.Refinement.Atlas206.High.Certificate

/-!
# Atlas 206: density range and optimality of `T_k`

`paper.pdf`, Table 1:

* the Goodman-type lower bound holds for `p ≥ 3/4`;
* `T_k` is optimal for every `k ≥ 4`.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Taeyoung.Paper.Refinements.Graph206

open Taeyoung Taeyoung.Paper Taeyoung.Methods.PureChordal Taeyoung.Methods.Negative

/-- **Lower bound range** (Table 1): the Goodman-type bound holds
for every graphon of edge density `p ≥ 3/4`.  Rational six-point certificates,
`Methods/RootedSOS/Refinement/Atlas206/`. -/
theorem lowerBoundRange : SatisfiesLowerBoundOn Taeyoung.Examples.Graph206.graph (Set.Ici (3 / 4)) :=
  (SatisfiesLowerBoundOn.Ici_of_Icc Taeyoung.Methods.RootedSOS.Refinement.Atlas206.High.satisfiesLowerBoundOn)

/-- **`T_k` is optimal for every `k ≥ 4`.** -/
theorem turanOptimal (k : ℕ) [NeZero k] (hk : 4 ≤ k) : TuranOptimal Taeyoung.Examples.Graph206.graph k :=
  turanOptimal_of_satisfiesLowerBoundOn lowerBoundRange k
    (mem_Ici_turanDensity (m := 4) (by norm_num) hk (by norm_num))

end Taeyoung.Paper.Refinements.Graph206
