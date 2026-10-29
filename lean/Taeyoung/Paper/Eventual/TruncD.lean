import Taeyoung.Paper.Eventual.TruncC

/-!
# Quantitative truncation, conclusion (`paper.pdf`, Proposition 4.15)

* `Dfun_high_ge_mean`: if `s ≤ δ/2` and `(n-3)s ≤ 1/2`, then `D_H(U₁) ≥ (c_* δ/16) q₁`, where
  `U₁ = highPart U δ` and `q₁ = ∫ U₁`;
* `one_le_cstar`: `c_* = ∑_v (d_H(v)-1)_+ ≥ 1` when `H` has a cycle;
* `truncation`: with `δ = (6n⁶)⁻¹`, if `Γ_H(K) ≥ 0` for every graphon `K` whose
  degree function is at most `δ`, then `Γ_H(U) ≥ 0` whenever `∫ U < δ²/2`.
-/

open MeasureTheory Finset SimpleGraph Polynomial

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- `c_* = ∑_v (d_H(v) - 1)_+`. -/
noncomputable def cstar (H : SimpleGraph V) [DecidableRel H.Adj] : ℝ :=
  ∑ v, ((H.degree v - 1 : ℕ) : ℝ)

lemma cstar_nonneg : 0 ≤ cstar H := Finset.sum_nonneg fun v _ ↦ Nat.cast_nonneg _

/-- A graph with a cycle has a vertex of degree at least two, so `c_* ≥ 1`. -/
lemma one_le_cstar (hcyc : ¬ H.IsAcyclic) : 1 ≤ cstar H := by
  classical
  obtain ⟨F, hF, hcard, v, hv⟩ := exists_adjacent_open hcyc
  have hFE := (mem_forests.mp (mem_openForests.mp hF).1).1
  obtain ⟨f₁, f₂, hne, rfl⟩ := Finset.card_eq_two.mp hcard
  obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp (hv _ (Finset.mem_insert_self _ _))
  obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp (hv f₂ (by simp))
  have ha : H.Adj v a := SimpleGraph.mem_edgeFinset.mp (hFE (Finset.mem_insert_self _ _))
  have hb : H.Adj v b := SimpleGraph.mem_edgeFinset.mp
    (hFE (show s(v, b) ∈ ({s(v, a), s(v, b)} : Finset (Sym2 V)) by simp))
  have hab : a ≠ b := fun h ↦ hne (by rw [h])
  have hdeg : 2 ≤ H.degree v := by
    rw [← H.card_neighborFinset_eq_degree]
    have hsub : ({a, b} : Finset V) ⊆ H.neighborFinset v := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (H.mem_neighborFinset v x).mpr ha
      · rw [Finset.mem_singleton.mp hx]; exact (H.mem_neighborFinset v b).mpr hb
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hab] at this
  unfold cstar
  have h1 : (1 : ℝ) ≤ ((H.degree v - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ H.degree v - 1)
  have h2 := Finset.single_le_sum (f := fun u ↦ ((H.degree u - 1 : ℕ) : ℝ))
    (fun u _ ↦ Nat.cast_nonneg _) (mem_univ v)
  linarith

/-- **(4.35), (4.36)** (with `g` in place of `h`) and the
resulting bound `D_H(U₁) ≥ (c_* δ/16) q₁`, `U₁ = highPart U δ`. -/
theorem Dfun_high_ge_mean (U : Graphon Ω μ) {δ : ℝ} (hδ : 0 < δ) (hs : sA U δ ≤ δ / 2)
    (hsn : ((Fintype.card V - 3 : ℕ) : ℝ) * sA U δ ≤ 1 / 2) :
    cstar H * δ / 16 * meanDeg (highPart U δ) ≤ Dfun H (highPart U δ) := by
  have hst : tA U δ = 1 - sA U δ := by have := sA_add_tA U δ; linarith
  have hs0 : 0 ≤ sA U δ := sA_nonneg U δ
  -- `t^{n-3} ≥ 1/2`
  have ht : (1 : ℝ) / 2 ≤ tA U δ ^ (Fintype.card V - 3) := by
    have := one_add_mul_le_pow (a := -sA U δ) (by linarith [tA_nonneg U δ]) (Fintype.card V - 3)
    rw [hst]
    have h2 : 1 + ((Fintype.card V - 3 : ℕ) : ℝ) * -sA U δ =
        1 - ((Fintype.card V - 3 : ℕ) : ℝ) * sA U δ := by ring
    rw [h2, ← sub_eq_add_neg] at this
    linarith
  -- on `A`, `g ≥ δ/2`
  have hgA : ∀ y, y ∈ excSet U δ → δ / 2 ≤ gA U δ y := by
    intro y hy
    have h1 := degree_le_sA_add_gA U δ y
    have h2 : δ < degree U y := hy
    linarith
  have hind := IsBdd.of_bddFun (indA U δ)
  have hgb := isBdd_gA U δ
  have hint_g : 0 ≤ ∫ y, indA U δ y * gA U δ y ∂μ :=
    integral_nonneg fun y ↦ mul_nonneg (indBdd_nonneg _ y) (gA_nonneg U δ y)
  -- `∫_A g² ≥ (δ/2) ∫_A g`
  have hsq : δ / 2 * ∫ y, indA U δ y * gA U δ y ∂μ ≤ ∫ y, indA U δ y * gA U δ y ^ 2 ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono ((hind.mul hgb).integrable.const_mul _) (hind.mul hgb.sq).integrable
      fun y ↦ ?_
    simp only [indA, indBdd_apply]
    by_cases hy : y ∈ excSet U δ
    · simp only [hy, Set.indicator_of_mem, Pi.one_apply, one_mul]
      have := hgA y hy
      nlinarith
    · simp [hy]
  -- `∫ (highPart U δ) ≤ 4 ∫_A g`
  have hmass : meanDeg (highPart U δ) ≤ 4 * ∫ y, indA U δ y * gA U δ y ∂μ := by
    refine (meanDeg_high_le U δ).trans ?_
    have : ∫ x, indA U δ x * degree U x ∂μ ≤ ∫ y, indA U δ y * (2 * gA U δ y) ∂μ := by
      refine integral_mono (hind.mul (isBdd_degree U)).integrable
        (hind.mul ((IsBdd.const 2).mul hgb)).integrable fun y ↦ ?_
      simp only [indA, indBdd_apply]
      by_cases hy : y ∈ excSet U δ
      · simp only [hy, Set.indicator_of_mem, Pi.one_apply, one_mul]
        have h1 := degree_le_sA_add_gA U δ y
        have h2 := hgA y hy
        linarith
      · simp [hy]
    have h2 : ∫ y, indA U δ y * (2 * gA U δ y) ∂μ = 2 * ∫ y, indA U δ y * gA U δ y ∂μ := by
      rw [← integral_const_mul]; refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only []; ring
    linarith
  have hD := Dfun_high_ge (H := H) U δ
  have hc0 : 0 ≤ cstar H := cstar_nonneg
  have hcs : cstar H = ∑ v, ((H.degree v - 1 : ℕ) : ℝ) := rfl
  rw [← hcs] at hD
  have hgsq0 : 0 ≤ ∫ y, indA U δ y * gA U δ y ^ 2 ∂μ :=
    integral_nonneg fun y ↦ mul_nonneg (indBdd_nonneg _ y) (sq_nonneg _)
  have e1 : cstar H * (1 / 2) * ∫ y, indA U δ y * gA U δ y ^ 2 ∂μ ≤
      cstar H * tA U δ ^ (Fintype.card V - 3) * ∫ y, indA U δ y * gA U δ y ^ 2 ∂μ := by
    apply mul_le_mul_of_nonneg_right _ hgsq0
    exact mul_le_mul_of_nonneg_left ht hc0
  have e2 : cstar H * (1 / 2) * (δ / 2 * ∫ y, indA U δ y * gA U δ y ∂μ) ≤
      cstar H * (1 / 2) * ∫ y, indA U δ y * gA U δ y ^ 2 ∂μ :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have e3 : cstar H * δ / 16 * meanDeg (highPart U δ) ≤
      cstar H * δ / 16 * (4 * ∫ y, indA U δ y * gA U δ y ∂μ) :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  have e4 : cstar H * δ / 16 * (4 * ∫ y, indA U δ y * gA U δ y ∂μ) =
      cstar H * (1 / 2) * (δ / 2 * ∫ y, indA U δ y * gA U δ y ∂μ) := by ring
  linarith

/-- **Proposition 4.15** for `H` of odd girth and `δ = (6n⁶)⁻¹`;
then `16m²δ ≤ 1`, so the threshold is `q < δ²/2`. -/
theorem truncation (hodd : Odd H.girth) {P : ℝ[X]} (hP : IsChromaticPolynomial H P)
    (U : Graphon Ω μ)
    (hlocal : ∀ K : Graphon Ω μ,
      (∀ x, degree K x ≤ 1 / (6 * (Fintype.card V : ℝ) ^ 6)) → 0 ≤ gammaFun H P K)
    (hq : meanDeg U < (1 / (6 * (Fintype.card V : ℝ) ^ 6)) ^ 2 / 2) :
    0 ≤ gammaFun H P U := by
  classical
  set n := Fintype.card V
  set δ : ℝ := 1 / (6 * (n : ℝ) ^ 6) with hδdef
  have hcyc : ¬ H.IsAcyclic := by
    intro hac
    have : H.girth = 0 := girth_eq_zero.mpr hac
    rw [this] at hodd; exact absurd hodd (by decide)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (H.three_le_girth hcyc).trans (girth_le_card hcyc)
  have hn6 : (729 : ℝ) ≤ (n : ℝ) ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num) hn3 6; norm_num at this; linarith
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hnδ : (n : ℝ) * δ ≤ 1 := by
    rw [hδdef, mul_one_div, div_le_one (by positivity)]
    have : (n : ℝ) ≤ (n : ℝ) ^ 6 :=
      calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hδ1 : δ ≤ 1 / 6 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hmn : (H.edgeFinset.card : ℝ) ≤ (n : ℝ) ^ 2 / 2 := card_edgeFinset_le
  have hm0 : (0 : ℝ) ≤ (H.edgeFinset.card : ℝ) := Nat.cast_nonneg _
  have hq0 : 0 ≤ meanDeg U := meanDeg_nonneg U
  -- the exceptional set is small
  have hMarkov := mul_sA_le U δ hδ.le
  have hs0 := sA_nonneg U δ
  have hs : sA U δ ≤ δ / 2 := by
    by_contra h
    push_neg at h
    have : δ * (δ / 2) < δ * sA U δ := mul_lt_mul_of_pos_left h hδ
    linarith
  have hsn : ((n - 3 : ℕ) : ℝ) * sA U δ ≤ 1 / 2 := by
    have h1 : ((n - 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 3
    have h2 : ((n - 3 : ℕ) : ℝ) * sA U δ ≤ (n : ℝ) * (δ / 2) :=
      mul_le_mul h1 hs hs0 (by positivity)
    nlinarith
  -- the split
  have hq12 : meanDeg (highPart U δ) + meanDeg (lowPart U δ) = meanDeg U :=
    meanDeg_high_add_low U δ
  have hq1 : 0 ≤ meanDeg (highPart U δ) := meanDeg_nonneg _
  have hq2 : 0 ≤ meanDeg (lowPart U δ) := meanDeg_nonneg _
  have hlow : 0 ≤ gammaFun H P (lowPart U δ) := hlocal (lowPart U δ) (degree_low_le U δ hδ.le)
  have hsup := Dfun_superadd (H := H) (highPart U δ) (lowPart U δ) U (high_add_low U δ)
  have hhigh := Dfun_high_ge_mean (H := H) U hδ hs hsn
  have h6δ : (n : ℝ) ^ 6 * δ = 1 / 6 := by rw [hδdef]; field_simp
  have hmq : (H.edgeFinset.card : ℝ) * meanDeg U ≤ 1 / 2 := by
    have h1 : meanDeg U ≤ δ ^ 2 / 2 := hq.le
    have h2 : (H.edgeFinset.card : ℝ) * meanDeg U ≤ (n : ℝ) ^ 2 / 2 * (δ ^ 2 / 2) :=
      mul_le_mul hmn h1 hq0 (by positivity)
    have h3 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h4 : (n : ℝ) ^ 2 * δ ≤ 1 / 6 := by
      have := mul_le_mul_of_nonneg_right h3 hδ.le; linarith
    have h5 : (n : ℝ) ^ 2 / 2 * (δ ^ 2 / 2) = ((n : ℝ) ^ 2 * δ) * δ / 4 := by ring
    have h6 : ((n : ℝ) ^ 2 * δ) * δ ≤ 1 / 6 * (1 / 6) :=
      mul_le_mul h4 hδ1 hδ.le (by norm_num)
    linarith
  have hrem := abs_remPoly_sub_le H.edgeFinset hq2 (by linarith) hmq
  rw [gammaFun_eq hcyc hP] at hlow ⊢
  have hc1 := one_le_cstar hcyc (H := H)
  -- `2 m² q ≤ c_* δ / 16`
  have hcoef : 2 * (H.edgeFinset.card : ℝ) ^ 2 * meanDeg U ≤ cstar H * δ / 16 := by
    have h1 : (H.edgeFinset.card : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 / 4 := by
      have := pow_le_pow_left₀ hm0 hmn 2
      calc (H.edgeFinset.card : ℝ) ^ 2 ≤ ((n : ℝ) ^ 2 / 2) ^ 2 := this
        _ = (n : ℝ) ^ 4 / 4 := by ring
    have h2 : meanDeg U ≤ δ ^ 2 / 2 := hq.le
    have h3 : (n : ℝ) ^ 4 * δ ≤ 1 / 54 := by
      rw [hδdef]
      have : (n : ℝ) ^ 4 / (6 * (n : ℝ) ^ 6) = 1 / (6 * (n : ℝ) ^ 2) := by
        field_simp
      rw [mul_one_div, this, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h4 : 2 * (H.edgeFinset.card : ℝ) ^ 2 * meanDeg U ≤ 2 * ((n : ℝ) ^ 4 / 4) * (δ ^ 2 / 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 hq0 (by positivity)
    have h5 : 2 * ((n : ℝ) ^ 4 / 4) * (δ ^ 2 / 2) = (n : ℝ) ^ 4 * δ * δ / 4 := by ring
    have h6 : (n : ℝ) ^ 4 * δ * δ / 4 ≤ δ / 16 := by
      have := mul_le_mul_of_nonneg_right h3 hδ.le
      nlinarith
    have h7 : δ / 16 ≤ cstar H * δ / 16 := by nlinarith
    linarith
  have hkey : meanDeg U - meanDeg (lowPart U δ) = meanDeg (highPart U δ) := by linarith
  rw [hkey] at hrem
  have hfin : 2 * (H.edgeFinset.card : ℝ) ^ 2 * meanDeg U * meanDeg (highPart U δ) ≤ cstar H * δ / 16 * meanDeg (highPart U δ) :=
    mul_le_mul_of_nonneg_right hcoef hq1
  have habs := le_abs_self (remPoly H.edgeFinset (meanDeg U) -
    remPoly H.edgeFinset (meanDeg (lowPart U δ)))
  linarith

end Taeyoung.Paper.Eventual
