import Taeyoung.Paper.Refinements.Basic
import Taeyoung.Examples.Graph129
import Taeyoung.Paper.Eventual.EvenGirth

/-!
# Atlas 129: density range and optimality of `T_k`

`paper.pdf`, Table 1:


* `T_k` is not optimal for any `k ≥ 4`.
-/

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Taeyoung.Paper.Refinements.Graph129

open Taeyoung Taeyoung.Paper Taeyoung.Methods.PureChordal Taeyoung.Methods.Negative

/-- The chromatic polynomial of Atlas 129, evaluated at a real point. -/
theorem count_real (m : ℕ) :
    (properAssignmentCount Taeyoung.Examples.Graph129.graph m : ℝ) =
      (fun k : ℝ ↦ (-10)*k^1 + (29)*k^2 + (-34)*k^3 + (21)*k^4 + (-7)*k^5 + (1)*k^6) (m : ℝ) := by
  rw [← Taeyoung.Examples.Graph129.chromPoly m]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    Finset.prod_range_succ, Finset.prod_range_zero,
    Taeyoung.Examples.Graph129.surj_0, Taeyoung.Examples.Graph129.surj_1, Taeyoung.Examples.Graph129.surj_2, Taeyoung.Examples.Graph129.surj_3, Taeyoung.Examples.Graph129.surj_4, Taeyoung.Examples.Graph129.surj_5, Taeyoung.Examples.Graph129.surj_6,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  norm_num [Nat.factorial]
  ring

theorem edgeCard : Taeyoung.Examples.Graph129.graph.edgeFinset.card = 7 := by
  rw [Taeyoung.Examples.Graph129.edgeFinset_eq]
  decide

/-- **`T_k` is not optimal for any `k ≥ 4`: the constant graphon.**  `W ≡ 1 - 1/k` has
`t(H,T_k) - t(H,W) = (k-1)(k³-5k²+6k-1)/k⁷ > 0` (Section 5.2). -/
theorem not_turanOptimal_constant (k : ℕ) [NeZero k] (hk : 4 ≤ k) :
    ¬ TuranOptimal Taeyoung.Examples.Graph129.graph k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hc0 : (0 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hk1
    linarith
  have hc1 : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  refine not_turanOptimal_of_lt (Eventual.constGraphon (1 - 1 / (k : ℝ)) hc0 hc1)
    (Eventual.edgeDensity_constGraphon _ _ _) ?_
  rw [Eventual.homDensity_constGraphon, edgeCard, homDensity_balancedMultipartite, count_real,
    Fintype.card_fin]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 4 := ⟨k - 4, by omega⟩
  push_cast
  rw [show (1 : ℝ) - 1 / ((n : ℝ) + 4) = ((n : ℝ) + 3) / ((n : ℝ) + 4) by field_simp; ring,
    div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : 0 < ((fun k : ℝ ↦ (-10)*k^1 + (29)*k^2 + (-34)*k^3 + (21)*k^4 + (-7)*k^5 + (1)*k^6) ((n : ℝ) + 4)) * ((n : ℝ) + 4) ^ 7 -
      ((n : ℝ) + 3) ^ 7 * ((n : ℝ) + 4) ^ 6 := by
    simp only
    ring_nf
    positivity
  simp only at key
  linarith

/-- **`T_k` is not optimal for any `k ≥ 4`: the tensor product.**  `T_{2k-1} ⊗ T_{2k}`, of edge
density `1 - 1/k`, has a smaller `H`-density than `T_k` (Section 5.2). -/
theorem not_turanOptimal_tensor (k : ℕ) [NeZero k] (hk : 4 ≤ k) :
    ¬ TuranOptimal Taeyoung.Examples.Graph129.graph k := by
  haveI : NeZero (2 * k - 1) := ⟨by omega⟩
  haveI : NeZero (2 * k) := ⟨by omega⟩
  refine not_turanOptimal_of_tensor k (2 * k - 1) (2 * k) (tensorTuran_density_double k (by omega)) ?_
  rw [count_real, count_real, count_real, Fintype.card_fin]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 4 := ⟨k - 4, by omega⟩
  have hcast : ((2 * (n + 4) - 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 7 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : 0 < ((fun k : ℝ ↦ (-10)*k^1 + (29)*k^2 + (-34)*k^3 + (21)*k^4 + (-7)*k^5 + (1)*k^6) ((n : ℝ) + 4)) * ((2 * (n : ℝ) + 7) * (2 * ((n : ℝ) + 4))) ^ 6 -
      ((fun k : ℝ ↦ (-10)*k^1 + (29)*k^2 + (-34)*k^3 + (21)*k^4 + (-7)*k^5 + (1)*k^6) (2 * (n : ℝ) + 7)) * ((fun k : ℝ ↦ (-10)*k^1 + (29)*k^2 + (-34)*k^3 + (21)*k^4 + (-7)*k^5 + (1)*k^6) (2 * ((n : ℝ) + 4))) *
        ((n : ℝ) + 4) ^ 6 := by
    simp only
    ring_nf
    positivity
  simp only at key ⊢
  linarith

end Taeyoung.Paper.Refinements.Graph129
