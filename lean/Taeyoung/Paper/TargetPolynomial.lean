import Taeyoung.Paper.Turan

/-!
# The target `Φ_H` as a polynomial in `p`

`Foundation/ChromaticTarget.lean` defines the target pointwise,
`Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` for `p ≠ 1` and `Φ_H(1) = 1`.  The paper
notes after (1.1) that this expression, initially defined for `p < 1`,
extends to a polynomial with `Φ_H(1) = 1` since `P_H` is monic of degree `v(H)`;
the lifting argument (Proposition 3.2) differentiates it twice.  This file supplies that polynomial,

```
targetPoly n P = ∑_{i ≤ n} P_i (1 - X)^{n - i},
```

and proves that it agrees with `chromaticTarget` everywhere, the endpoint
included, for every chromatic polynomial (`chromaticTarget_eq_eval_targetPoly`).
The endpoint needs that a chromatic polynomial is monic of degree `v(H)`
(`IsChromaticPolynomial.natDegree_le`, `IsChromaticPolynomial.coeff_card`),
which we read off from the surjective-count expansion of
`Methods/Negative/Chromatic.lean`.
-/

open MeasureTheory Polynomial Finset

namespace Taeyoung.Paper

open Taeyoung

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Chromatic polynomials are monic of degree `v(H)` -/

/-- The falling-factorial polynomial `X(X-1)⋯(X-j+1)`. -/
noncomputable def fallingPoly (j : ℕ) : ℝ[X] := ∏ i ∈ range j, (X - C (i : ℝ))

lemma fallingPoly_monic (j : ℕ) : (fallingPoly j).Monic :=
  monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C _

lemma fallingPoly_natDegree (j : ℕ) : (fallingPoly j).natDegree = j := by
  rw [fallingPoly, natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- A surjection onto `Fin |V|` is a bijection, hence proper for every graph. -/
theorem surjCount_card_eq (H : SimpleGraph V) [DecidableRel H.Adj] :
    Methods.Negative.surjCount H (Fintype.card V) = (Fintype.card V).factorial := by
  classical
  have hset : ((univ : Finset (V → Fin (Fintype.card V))).filter
      (fun y ↦ Methods.Negative.IsProper H y ∧ Function.Surjective y)) =
      (univ : Finset (V → Fin (Fintype.card V))).filter Function.Injective := by
    refine Finset.filter_congr fun y _ ↦ ?_
    constructor
    · rintro ⟨-, hs⟩
      exact ((Fintype.bijective_iff_surjective_and_card y).mpr ⟨hs, by simp⟩).1
    · intro hy
      exact ⟨fun _ _ huv hc ↦ huv.ne (hy hc),
        ((Fintype.bijective_iff_injective_and_card y).mpr ⟨hy, by simp⟩).2⟩
  rw [Methods.Negative.surjCount, hset, ← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq]
  simp [Nat.descFactorial_self]

/-- The surjective-count expansion, in terms of `fallingPoly`. -/
lemma isChromaticPolynomial_surj (H : SimpleGraph V) [DecidableRel H.Adj] :
    IsChromaticPolynomial H (∑ j ∈ range (Fintype.card V + 1),
      C ((Methods.Negative.surjCount H j : ℝ) / (j).factorial) * fallingPoly j) :=
  Methods.Negative.isChromaticPolynomial_of_surjCount H

/-- **A chromatic polynomial has degree at most `v(H)`.** -/
theorem _root_.Taeyoung.IsChromaticPolynomial.natDegree_le {H : SimpleGraph V} [DecidableRel H.Adj]
    {P : ℝ[X]} (hP : IsChromaticPolynomial H P) : P.natDegree ≤ Fintype.card V := by
  rw [IsChromaticPolynomial.unique H hP (isChromaticPolynomial_surj H)]
  refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [fallingPoly_natDegree]
  exact Nat.lt_succ_iff.mp (mem_range.mp hj)

/-- **A chromatic polynomial has leading coefficient one in degree `v(H)`.** -/
theorem _root_.Taeyoung.IsChromaticPolynomial.coeff_card {H : SimpleGraph V} [DecidableRel H.Adj]
    {P : ℝ[X]} (hP : IsChromaticPolynomial H P) : P.coeff (Fintype.card V) = 1 := by
  rw [IsChromaticPolynomial.unique H hP (isChromaticPolynomial_surj H), finsetSum_coeff,
    Finset.sum_eq_single (Fintype.card V)]
  · have hmon := (fallingPoly_monic (Fintype.card V)).coeff_natDegree
    rw [fallingPoly_natDegree] at hmon
    rw [coeff_C_mul, hmon, surjCount_card_eq]
    have : ((Fintype.card V).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · intro j hj hjn
    have hjlt : j < Fintype.card V := by
      have := Nat.lt_succ_iff.mp (mem_range.mp hj)
      omega
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [fallingPoly_natDegree]; exact hjlt),
      mul_zero]
  · intro h
    exact absurd (mem_range.mpr (Nat.lt_succ_self _)) h

/-! ### The target polynomial -/

/-- `Φ` as a polynomial in `p`: `∑_{i ≤ n} P_i (1 - p)^{n-i}`. -/
noncomputable def targetPoly (n : ℕ) (P : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ range (n + 1), C (P.coeff i) * (1 - X) ^ (n - i)

lemma eval_targetPoly (n : ℕ) (P : ℝ[X]) (z : ℝ) :
    (targetPoly n P).eval z = ∑ i ∈ range (n + 1), P.coeff i * (1 - z) ^ (n - i) := by
  simp [targetPoly, eval_finsetSum]

/-- Away from `p = 1`, the target polynomial is the literal expression. -/
lemma eval_targetPoly_of_ne_one {n : ℕ} {P : ℝ[X]} (hdeg : P.natDegree ≤ n) {z : ℝ}
    (hz : z ≠ 1) :
    (targetPoly n P).eval z = (1 - z) ^ n * P.eval (1 / (1 - z)) := by
  have hq : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  rw [eval_targetPoly, eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hsplit : (1 - z) ^ n = (1 - z) ^ (n - i) * (1 - z) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [hsplit, div_pow, one_pow]
  field_simp

/-- At `p = 1` the target polynomial reads off the coefficient of `X^n`. -/
lemma eval_targetPoly_one (n : ℕ) (P : ℝ[X]) :
    (targetPoly n P).eval 1 = P.coeff n := by
  rw [eval_targetPoly, sub_self, Finset.sum_eq_single n]
  · simp
  · intro i hi hin
    have : i < n := by
      have := Nat.lt_succ_iff.mp (mem_range.mp hi)
      omega
    rw [zero_pow (by omega), mul_zero]
  · intro h
    exact absurd (mem_range.mpr (Nat.lt_succ_self _)) h

/-- **The pointwise target is the target polynomial**, endpoint included. -/
theorem chromaticTarget_eq_eval_targetPoly {H : SimpleGraph V} [DecidableRel H.Adj]
    {P : ℝ[X]} (hP : IsChromaticPolynomial H P) (p : ℝ) :
    chromaticTarget (V := V) P p = (targetPoly (Fintype.card V) P).eval p := by
  by_cases hp : p = 1
  · subst hp
    rw [chromaticTarget_at_one, eval_targetPoly_one, hP.coeff_card]
  · rw [chromaticTarget_of_ne_one P hp, eval_targetPoly_of_ne_one hP.natDegree_le hp]

/-- The target polynomial of a disjoint union is the product. -/
theorem targetPoly_mul {m n : ℕ} {P₁ P₂ : ℝ[X]} (h₁ : P₁.natDegree ≤ m)
    (h₂ : P₂.natDegree ≤ n) (hc₁ : P₁.coeff m = 1) (hc₂ : P₂.coeff n = 1) :
    targetPoly (m + n) (P₁ * P₂) = targetPoly m P₁ * targetPoly n P₂ := by
  apply Polynomial.funext
  intro z
  rw [eval_mul]
  by_cases hz : z = 1
  · subst hz
    rw [eval_targetPoly_one, eval_targetPoly_one, eval_targetPoly_one,
      coeff_mul_add_eq_of_natDegree_le h₁ h₂]
  · rw [eval_targetPoly_of_ne_one ((natDegree_mul_le).trans (add_le_add h₁ h₂)) hz,
      eval_targetPoly_of_ne_one h₁ hz, eval_targetPoly_of_ne_one h₂ hz, eval_mul, pow_add]
    ring

end Taeyoung.Paper
