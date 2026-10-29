import Taeyoung.Paper.Refinements.Basic
import Taeyoung.Paper.Refinements.Graph048
import Taeyoung.Paper.Refinements.Graph050
import Taeyoung.Paper.Refinements.Graph129
import Taeyoung.Paper.Refinements.Graph140
import Taeyoung.Paper.Refinements.Graph141
import Taeyoung.Paper.Refinements.Graph143
import Taeyoung.Paper.Refinements.Graph149
import Taeyoung.Paper.Refinements.Graph152
import Taeyoung.Paper.Refinements.Graph158
import Taeyoung.Paper.Refinements.Graph159
import Taeyoung.Paper.Refinements.Graph166
import Taeyoung.Paper.Refinements.Graph170
import Taeyoung.Paper.Refinements.Graph172
import Taeyoung.Paper.Refinements.Graph173
import Taeyoung.Paper.Refinements.Graph182
import Taeyoung.Paper.Refinements.Graph184
import Taeyoung.Paper.Refinements.Graph186
import Taeyoung.Paper.Refinements.Graph189
import Taeyoung.Paper.Refinements.Graph190
import Taeyoung.Paper.Refinements.Graph197
import Taeyoung.Paper.Refinements.Graph198
import Taeyoung.Paper.Refinements.Graph204
import Taeyoung.Paper.Refinements.Graph206

/-!
# Density ranges and optimality of `T_k` for the violating graphs

`paper.pdf`, Section 5.1 and Section 5.2.  For
each of the 23 graphs violating the Goodman-type lower bound, the module
`Paper/Refinements/GraphNNN.lean` (namespace `Taeyoung.Paper.Refinements.GraphNNN`)
proves its row of Table 1 about the catalogue graph
`Taeyoung.Examples.GraphNNN.graph`:

* `lowerBoundRange : SatisfiesLowerBoundOn graph S` — the Goodman-type bound for
  every graphon of edge density in `S`;
* `turanOptimal k (hk : k₀ ≤ k) : TuranOptimal graph k`;
* `not_turanOptimal_three`, `_four`, `_five : ¬ TuranOptimal graph k`.

| Graphs | Lower bound range | Optimality of `T_k` |
|---|---|---|
| 152, 166, 172, 182, 184 | `p = 2/3` or `p ≥ 3/4` | optimal for every `k ≥ χ(H) = 3` |
| 206 | `p ≥ 3/4` | optimal for every `k ≥ χ(H) = 4` |
| 48, 50, 140, 141, 143, 158, 159, 197, 198 | `p ≥ 3/4` | not at `k = 3`; optimal for `k ≥ 4` |
| 186 | `p = 3/4` or `p ≥ 4/5` | not at `k = 3`; optimal for `k ≥ 4` |
| 190 | `p ≥ 4/5` | not at `k = 3, 4`; optimal for `k ≥ 5` |
| 173 | `p ≥ 4/5` | not at `k = 3`; optimal for `k ≥ 5` |
| 149, 170 | `p ≥ 1 - (72·6¹²)⁻¹` | not at `k = 3, 4, 5`; optimal for `k ≥ 72·6¹²` |
| 189, 204 | `p ≥ 1 - (72·6¹²)⁻¹` | not at `k = 3, 4`; optimal for `k ≥ 72·6¹²` |
| 129 | — | not at any `k ≥ 4` (`not_turanOptimal_constant`, `not_turanOptimal_tensor`) |

**Where the ranges come from.**  The ranges `p ≥ 3/4`, `p ≥ 4/5` and the single
densities `p = 2/3`, `p = 3/4` are rational six-point sum-of-squares certificates, checked in
`Methods/RootedSOS/Refinement/Atlas<ID>/{High,Turan3,Turan4}/`.  The ranges `p ≥ 1 - (72·6¹²)⁻¹`
are the explicit threshold of Theorem 1.6, closed at the endpoint by
`SatisfiesLowerBoundOn.Ici_of_Ioi`.  Optimality of `T_k` is the bound at
`p = 1 - 1/k` (`turanOptimal_of_satisfiesLowerBoundOn`).

**Where the counterexamples come from** (Section 5.2).

* `T_{2k-1} ⊗ T_{2k}`, of edge density `1 - 1/k` (`tensorTuran_density_double`,
  `Methods.Negative.homDensity_tensorTuran`): `not_turanOptimal_three` for
  Atlas 149, 170, 173, 186, 189, 190, 197, 198, 204, `not_turanOptimal_four` for
  149, 170, 189, 204, `not_turanOptimal_five` for 149, 170, and
  `Graph129.not_turanOptimal_tensor` for every `k ≥ 4`.
* Atlas 129: the constant graphon `W ≡ 1 - 1/k` (`Graph129.not_turanOptimal_constant`).
* Atlas 190 at `k = 4`: the four-part graphon `W_ε` with `ε = 1/100`
  (`Graph190.not_turanOptimal_four`); the paper takes `ε` sufficiently small.
* Atlas 48, 50, 140, 141, 143, 158: the four-part graphon
  `Methods.Negative.extraVertexW`; Atlas 159: the three-part graphon
  `Methods.Negative.threePartW` (`not_turanOptimal_three`).
* The catalogue rows `Taeyoung.Examples.GraphNNN.status` use the same constructions:
  `T₅ ⊗ T₆`, `T₄ ⊗ T₄` (Atlas 182, 184), `W ≡ 3/4` (Atlas 129), the four-part and
  three-part graphons above, `Methods.Negative.twoScaleW` (Atlas 166, 172),
  `Methods.Negative.oneDiagW` (Atlas 206), and `Methods.Negative.W152`, the
  graphon `W_ε` of Atlas 152 at `ε = 1/3000`.

The 94 graphs satisfying (1.2) have `T_k` optimal for every `k ≥ χ(H)` by
`Taeyoung.Paper.turanOptimal_of_satisfiesLowerBound`.  Of (5.1),
the upper bound `t(H_173, T_4) = 9/128` is `Graph173.turan4_value`; the lower bound
`14056671/200000000`, a seven-point certificate, is not formalized.
-/
