import Taeyoung.Paper.Basic
import Taeyoung.Paper.Turan
import Taeyoung.Paper.TargetPolynomial
import Taeyoung.Paper.Lifting
import Taeyoung.Paper.TriviallyPerfect
import Taeyoung.Paper.OddCycles
import Taeyoung.Paper.ChordalLeaves
import Taeyoung.Paper.Profile.Main
import Taeyoung.Paper.Eventual.Main

/-!
# The results of `paper.pdf`

Results are cited by their LaTeX labels.  Declarations without a namespace are in
`Taeyoung.Paper`; `Profile.`, `Eventual.` abbreviate `Taeyoung.Paper.Profile`,
`Taeyoung.Paper.Eventual`.

| Paper | Lean |
|---|---|
| `Φ_H`, (1.1) | `Taeyoung.chromaticTarget`; as a polynomial, `targetPoly` (`chromaticTarget_eq_eval_targetPoly`) |
| the Goodman-type lower bound, (1.2) | `Taeyoung.SatisfiesLowerBound` (stated on the closed range `p ≥ p̲_H`) |
| (1.3) | `homDensity_turan_eq_chromaticTarget`, `edgeDensity_turan` |
| (1.4), and (1.2) implies it | `TuranOptimal`, `turanOptimal_of_satisfiesLowerBound` |
| Theorem 1.1 | `Methods.PureChordal.pureChordal_satisfiesLowerBound` (and `Profile.pure_profileMonotone`) |
| Lemma 1.2 | `Profile.chordal_satisfiesLowerBound_of_profile` |
| `b_j`, (1.5) | `Profile.profileB`, `Profile.profileB_eq_sub` (the form `#{i : r_i ≥ j} - #{e : s_e ≥ j}`) |
| `P_H = ∏ (x-j+1)^{b_j}` and `χ(H) = k` | `Profile.isChromaticPolynomial_profilePoly` (in the form `∏_i ∏_{s_i ≤ j < r_i} (x-j)`), `Profile.isChromaticNumber_of_bags` |
| (2.2) | `Profile.chromaticTarget_profilePoly` |
| Proposition 2.1 | `Profile.gluing_inequality` |
| Lemma 2.2 (Moon–Moser) | `Methods.PureChordal.cliqueDensity_moonMoser_succ` |
| Lemma 2.3 | `Methods.PureChordal.cliqueDensity_step_lower` |
| Theorem 1.3 | `IsTriviallyPerfect.satisfiesLowerBound` |
| Theorem 1.4, (1.6) | `oddCycle_bound` (every density), `cycleGraph_satisfiesLowerBound`; from `OddCycleBound.odd_cycle_bound` |
| Corollary 1.5 | `oddJoin_satisfiesLowerBound` |
| Lemma 3.1 | `Methods.Link.weighted_rootedTriangle` |
| Proposition 3.2 | `lifting` |
| (3.3) | `iterated_lifting` |
| eventual satisfaction of the bound | `EventuallySatisfiesLowerBound` |
| Theorem 1.6, (i) ⇔ (ii) ⇔ (iii) | `Eventual.eventual_tfae_of_not_bipartite`; `Eventual.eventual_tfae` for every graph with a cycle |
| (1.7), `p_H = 1 - 1/(72n¹²)` and `k > 72n¹²` | `Eventual.satisfiesLowerBoundOn_threshold`, `Eventual.turanOptimal_of_odd_girth` |
| Lemma 4.2 | `Eventual.chromaticTarget_eq_forest_sum`, `Eventual.gamma_eq` (Kruskal intervals: `Eventual.sum_powerset_eq_sum_forests`) |
| Lemma 4.4, (4.9) | `Eventual.forest_variance`, `Eventual.Mom_variance` |
| Lemma 4.5, interval form | `Eventual.intervalInt_le_closing`, `Eventual.intervalInt_leading`, `Eventual.sum_intervalInt_le` |
| Lemma 4.6 | `Eventual.Qs_le_triangle` |
| Theorem 4.7 | `Eventual.cycle_comparison` |
| Lemma 4.8 | `Eventual.scalar_moment` |
| Lemma 4.9 | `Eventual.abs_ev_le`, `Eventual.hasSum_cyc`; (4.18) is replaced by Bessel's inequality `Eventual.tsum_weighted_le` |
| Lemma 4.10 | `Eventual.Ss_decomp` (with a nonnegative Bessel residual) |
| Lemma 4.11 | `Eventual.card_cycleSets_le` (in the form `#{s-cycles} ≤ n^{s-g+3}`) |
| Proposition 4.12 | `Eventual.local_estimate`, `Eventual.local_of_small_degree` (its final assertion) |
| Lemma 4.13 | `Eventual.Dfun_nonneg`, `Eventual.Dfun_superadd` |
| Lemma 4.14 | `Eventual.abs_remPoly_sub_le` |
| Proposition 4.15 | `Eventual.truncation` (with `δ = (6n⁶)⁻¹`) |
| Proposition 4.17 | `Eventual.not_turanOptimal_of_even_girth` |
| Theorem 1.7 | `Catalogue/Counts.lean` (117 rows, 94 positive, 23 negative) |
| Figure 2, the counterexamples of Section 5.2 | `Taeyoung.Examples.GraphNNN.status` for the 23 rows (witnesses in `Methods/Negative/`) |
| Table 1 | `Taeyoung.Paper.Refinements.GraphNNN.lowerBoundRange`, `.turanOptimal`, `.not_turanOptimal_three` (`_four`, `_five`); Atlas 129: `.not_turanOptimal_constant`, `.not_turanOptimal_tensor` (see `Paper/Refinements.lean`) |
| the 94 positive graphs have `T_k` optimal for every `k ≥ χ(H)` | `turanOptimal_of_satisfiesLowerBound` |
| `T_{2k-1} ⊗ T_{2k}` has edge density `1 - 1/k`; `t(H, U ⊗ V) = t(H,U)·t(H,V)` for Turán factors | `Refinements.tensorTuran_density_double`; `Methods.Negative.homDensity_tensorTuran` |
| (5.1), upper bound `t(H₁₇₃, T₄) = 9/128` | `Refinements.Graph173.turan4_value` |
| Proposition 6.1 | `leafTriangle_twenty_violates` |

Lean-side complements that the paper does not state: `TuranOptimal.le_of_le_edgeDensity`
(optimality transfers to larger edge densities by scaling) and
`satisfiesLowerBound_of_edgeless`.

Not formalized separately: Lemma 4.1 (the forest expansion is proved
directly), Lemma 4.3 (replaced by integrating leaves), and Lemma
4.16 (`not_turanOptimal_of_even_girth` reads off the leading term
directly).  Of (5.1) only the upper bound is formalized: the lower
bound `14056671/200000000` is a seven-point flag-algebra certificate
that is not checked in Lean.  The Lean witnesses for
the two families taken with `ε` sufficiently small in Section 5.2
use `ε = 1/3000` (Atlas 152) and `ε = 1/100` (Atlas 190 at `k = 4`).

Theorem 1.4 and the spectral theory behind Theorem 4.7 come
from the Lake dependency `OddCycleBound`, the formalization of Im, Kim, and Yang
(<https://github.com/mekty2012/OddCycleGoodman-lean>): `Paper/OddCycles.lean` and
`Paper/Eventual/Spectral.lean` are the bridges.
-/
