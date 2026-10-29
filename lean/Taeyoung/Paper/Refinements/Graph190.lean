import Taeyoung.Paper.Refinements.Basic
import Taeyoung.Examples.Graph190
import Taeyoung.Methods.RootedSOS.Refinement.Atlas190.High.Certificate
import Taeyoung.Methods.Negative.StepGraphon

/-!
# Atlas 190: density range and optimality of `T_k`

`paper.pdf`, Table 1:

* the Goodman-type lower bound holds for `p ≥ 4/5`;
* `T_k` is optimal for every `k ≥ 5`;
* `T_k` is not optimal for `k = 3, 4`.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Taeyoung.Paper.Refinements.Graph190

open Taeyoung Taeyoung.Paper Taeyoung.Methods.PureChordal Taeyoung.Methods.Negative

/-- **Lower bound range** (Table 1): the Goodman-type bound holds
for every graphon of edge density `p ≥ 4/5`.  Rational six-point certificates,
`Methods/RootedSOS/Refinement/Atlas190/`. -/
theorem lowerBoundRange : SatisfiesLowerBoundOn Taeyoung.Examples.Graph190.graph (Set.Ici (4 / 5)) :=
  (SatisfiesLowerBoundOn.Ici_of_Icc Taeyoung.Methods.RootedSOS.Refinement.Atlas190.High.satisfiesLowerBoundOn)

/-- **`T_k` is optimal for every `k ≥ 5`.** -/
theorem turanOptimal (k : ℕ) [NeZero k] (hk : 5 ≤ k) : TuranOptimal Taeyoung.Examples.Graph190.graph k :=
  turanOptimal_of_satisfiesLowerBoundOn lowerBoundRange k
    (mem_Ici_turanDensity (m := 5) (by norm_num) hk (by norm_num))

/-- **`T_3` is not optimal**: `T_5 ⊗ T_6`, of edge density `1 - 1/3`, has a smaller
`H`-density (Section 5.2). -/
theorem not_turanOptimal_three : ¬ TuranOptimal Taeyoung.Examples.Graph190.graph 3 := by
  have h5 : properAssignmentCount Taeyoung.Examples.Graph190.graph 5 = 1440 := by
    rw [Taeyoung.Examples.Graph190.count]; decide
  have h6 : properAssignmentCount Taeyoung.Examples.Graph190.graph 6 = 6720 := by
    rw [Taeyoung.Examples.Graph190.count]; decide
  have h3 : properAssignmentCount Taeyoung.Examples.Graph190.graph 3 = 12 := by
    rw [Taeyoung.Examples.Graph190.count]; decide
  refine not_turanOptimal_of_tensor 3 5 6 (by norm_num) ?_
  rw [h5, h6, h3, Fintype.card_fin]
  norm_num

/-! ### `T_4` is not optimal for Atlas 190

Section 5.2: on four equal parts, put `ε` on the diagonal and
`1 - ε/3` off it.  The edge density stays `3/4`, while
`d/dε t(H, W_ε)|_{ε=0} = -1/256`.  Here `ε = 1/100`: the values are `3/300` and
`299/300`. -/

/-- The values of `W_ε` at `ε = 1/100`, as numerators over `300`. -/
def epsN : Fin 4 → Fin 4 → ℕ := fun i j ↦ if i = j then 3 else 299

/-- `W_ε` at `ε = 1/100`. -/
noncomputable def epsW : Graphon (Fin 4) (finiteUniformMeasure (Fin 4)) :=
  stepGraphon 4 300 epsN (by decide) (by decide)

theorem eps_pairSum : ∑ z : Fin 2 → Fin 4, epsN (z 0) (z 1) = 3600 := by decide +kernel

theorem cliqueDensity_epsW : cliqueDensity 2 epsW = 3 / 4 := by
  rw [cliqueDensity_two_of_natWeight epsW (fun z ↦ epsN (z 0) (z 1)) ((300 : ℝ))
    (fun z ↦ rfl), eps_pairSum]
  norm_num

lemma edgeFinset_eq : Taeyoung.Examples.Graph190.graph.edgeFinset =
    {s(0, 1), s(0, 2), s(0, 5), s(1, 2), s(1, 3), s(1, 4), s(2, 5), s(3, 4), s(3, 5), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The natural-number numerator of the graph weight. -/
def epsNumerator (z : Fin 6 → Fin 4) : ℕ :=
    epsN (z 0) (z 1) *
    epsN (z 0) (z 2) *
    epsN (z 0) (z 5) *
    epsN (z 1) (z 2) *
    epsN (z 1) (z 3) *
    epsN (z 1) (z 4) *
    epsN (z 2) (z 5) *
    epsN (z 3) (z 4) *
    epsN (z 3) (z 5) *
    epsN (z 4) (z 5)

lemma graphWeight_nat (z : Fin 6 → Fin 4) :
    graphWeight Taeyoung.Examples.Graph190.graph epsW z = (epsNumerator z : ℝ) / (300 : ℝ) ^ 10 := by
  rw [graphWeight, edgeFinset_eq]
  simp [epsW, stepGraphon_apply, epsNumerator]
  ring

theorem eps_weightSum : ∑ z : Fin 6 → Fin 4, epsNumerator z = 1133202676669210959963230208 := by decide +kernel

/-- **`T_4` is not optimal**: `t(H, W_ε) < 3/64 = t(H, T_4)` at `ε = 1/100`. -/
theorem not_turanOptimal_four : ¬ TuranOptimal Taeyoung.Examples.Graph190.graph 4 := by
  refine not_turanOptimal_of_lt epsW ?_ ?_
  · show cliqueDensity 2 epsW = _
    rw [cliqueDensity_epsW]
    norm_num
  · have h4 : properAssignmentCount Taeyoung.Examples.Graph190.graph 4 = 192 := by
      rw [Taeyoung.Examples.Graph190.count]; decide
    rw [homDensity_of_natWeight _ epsW epsNumerator ((300 : ℝ) ^ 10) graphWeight_nat,
      eps_weightSum, homDensity_balancedMultipartite, h4, Fintype.card_fin]
    norm_num

end Taeyoung.Paper.Refinements.Graph190
