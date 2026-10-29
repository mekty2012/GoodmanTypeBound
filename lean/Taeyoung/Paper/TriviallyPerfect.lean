import Taeyoung.Paper.Lifting
import Taeyoung.Methods.Components.Atlas84

/-!
# Trivially perfect graphs (`paper.pdf`, Section 3.3, Theorem 1.3)

A graph is trivially perfect if it has no induced `P₄` or `C₄`; equivalently
(Wolk; see Drange–Pilipczuk), it is generated from `K₁` by disjoint unions and
the addition of a universal vertex.  The paper's proof inducts on that
generation, and so does this file: `TPGenerated` is the generated class, on the
vertex types `Fin n`, and `IsTriviallyPerfect H` says that `H` is isomorphic to a
member of it.  (The equivalence with the paper's definition by forbidden induced
`P₄` and `C₄`, which the paper takes from Drange–Pilipczuk, is not formalized.)

**Theorem 1.3.** Every trivially perfect graph with at least one edge satisfies
the Goodman-type lower bound (`IsTriviallyPerfect.satisfiesLowerBound`, which also
covers edgeless graphs, where both sides are `1`).

The induction carries, for every generated `F` with an edge, both the bound and
the sign profile of `Φ_F` on `[p̲_F, 1]` needed by `lifting`
(`tpGenerated_claim`):

* a **disjoint union** multiplies densities and targets; its admissible interval
  is that of the component of largest chromatic number, and products of
  nonnegative nondecreasing convex polynomials keep the three signs;
* a **cone over an edgeless graph** is a star, `t(K_{1,n},W) = ∫ dⁿ ≥ pⁿ = Φ`;
* a **cone over a graph with an edge** is `lifting` at `p̲_F = 1 - 1/(χ(F)-1)`,
  whose output threshold `1/(2 - p̲_F) = 1 - 1/χ(F)` is exactly `p̲_{K₁ ∨ F}`.
-/

open MeasureTheory Polynomial Finset

namespace Taeyoung.Paper

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.Components

/-! ### The generated class -/

/-- Graphs on `Fin n` generated from `K₁` by disjoint union and by adding a
universal vertex (`coneGraph`). -/
inductive TPGenerated : {n : ℕ} → SimpleGraph (Fin n) → Prop
  | single : TPGenerated (⊥ : SimpleGraph (Fin 1))
  | union {m n : ℕ} {G : SimpleGraph (Fin m)} {H : SimpleGraph (Fin n)} :
      TPGenerated G → TPGenerated H → TPGenerated (disjointUnion G H)
  | cone {n : ℕ} {G : SimpleGraph (Fin n)} : TPGenerated G → TPGenerated (coneGraph G)

/-- `H` is trivially perfect: isomorphic to a graph generated from `K₁` by
disjoint unions and universal vertices. -/
def IsTriviallyPerfect {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), TPGenerated G ∧ Nonempty (G ≃g H)

/-! ### Edgeless graphs, once more -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edgeless graph has chromatic polynomial `X^{v(H)}`. -/
lemma isChromaticPolynomial_of_edgeless (H : SimpleGraph V) [DecidableRel H.Adj]
    (hE : H.edgeFinset = ∅) : IsChromaticPolynomial H (X ^ Fintype.card V) := by
  classical
  intro k
  have : (Finset.univ.filter (IsProperAssignment H : (V → Fin k) → Prop)) =
      Finset.univ := by
    apply Finset.filter_true_of_mem
    intro x _ u v huv
    exfalso
    have : s(u, v) ∈ H.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact huv
    rw [hE] at this
    exact absurd this (Finset.notMem_empty _)
  rw [properAssignmentCount, this, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  simp

/-- An edgeless graph has target `Φ ≡ 1`. -/
lemma chromaticTarget_of_edgeless (H : SimpleGraph V) [DecidableRel H.Adj]
    (hE : H.edgeFinset = ∅) {P : ℝ[X]} (hP : IsChromaticPolynomial H P) (p : ℝ) :
    chromaticTarget (V := V) P p = 1 := by
  rw [IsChromaticPolynomial.unique H hP (isChromaticPolynomial_of_edgeless H hE)]
  by_cases hp : p = 1
  · rw [hp, chromaticTarget_at_one]
  · rw [chromaticTarget_of_ne_one _ hp, eval_pow, eval_X, ← mul_pow,
      mul_one_div_cancel (sub_ne_zero.mpr (Ne.symm hp)), one_pow]

/-- An edgeless graph has target polynomial `1`. -/
lemma targetPoly_of_edgeless (H : SimpleGraph V) [DecidableRel H.Adj]
    (hE : H.edgeFinset = ∅) {P : ℝ[X]} (hP : IsChromaticPolynomial H P) :
    targetPoly (Fintype.card V) P = 1 := by
  apply Polynomial.funext
  intro z
  rw [← chromaticTarget_eq_eval_targetPoly hP, chromaticTarget_of_edgeless H hE hP, eval_one]

/-- A graph is edgeless exactly when its chromatic number is at most one. -/
lemma edgeFinset_eq_empty_iff_chromaticNumber_le_one {H : SimpleGraph V}
    [DecidableRel H.Adj] {r : ℕ} (hr : IsChromaticNumber H r) :
    H.edgeFinset = ∅ ↔ r ≤ 1 := by
  refine ⟨fun hE ↦ ?_, edgeFinset_eq_empty_of_chromaticNumber_le_one hr⟩
  by_contra hr1
  have hz := hr.zero_below 1 (by omega)
  have h := isChromaticPolynomial_of_edgeless H hE 1
  simp only [Nat.cast_one, eval_pow, eval_X, one_pow] at h
  have h1 : properAssignmentCount H 1 = 1 := by exact_mod_cast h.symm
  omega

/-! ### Small facts about the thresholds -/

/-- `threshold r = 1 - 1/(r-1)`, the paper's `p̲_H` for `χ(H) = r`. -/
noncomputable def threshold (r : ℕ) : ℝ := 1 - 1 / (((r - 1 : ℕ) : ℝ))

lemma threshold_lt_one {r : ℕ} (hr : 2 ≤ r) : threshold r < 1 := by
  have h1 : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < r - 1 by omega)
  have : 0 < 1 / ((r - 1 : ℕ) : ℝ) := by positivity
  unfold threshold; linarith

lemma threshold_mono {r s : ℕ} (hr : 2 ≤ r) (hrs : r ≤ s) : threshold r ≤ threshold s := by
  have h1 : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < r - 1 by omega)
  have h2 : ((r - 1 : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by exact_mod_cast (show r - 1 ≤ s - 1 by omega)
  have : 1 / ((s - 1 : ℕ) : ℝ) ≤ 1 / ((r - 1 : ℕ) : ℝ) := one_div_le_one_div_of_le h1 h2
  unfold threshold; linarith

/-- Lifting at `threshold r` gives `threshold (r + 1)`: `1/(2 - p̲_F) = p̲_{K₁ ∨ F}`. -/
lemma lift_threshold {r : ℕ} (hr : 2 ≤ r) : 1 / (2 - threshold r) = threshold (r + 1) := by
  have h1 : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < r - 1 by omega)
  have hcast : ((r + 1 - 1 : ℕ) : ℝ) = ((r - 1 : ℕ) : ℝ) + 1 := by
    rw [show r + 1 - 1 = (r - 1) + 1 by omega]; push_cast; ring
  unfold threshold
  rw [hcast]
  set s := ((r - 1 : ℕ) : ℝ) with hs
  have hs0 : s ≠ 0 := h1.ne'
  have hs1 : s + 1 ≠ 0 := by linarith
  have hs2 : 2 - (1 - 1 / s) = (s + 1) / s := by field_simp; ring
  rw [hs2, one_div_div, eq_sub_iff_add_eq, ← add_div, div_self hs1]

/-! ### Profiles of products -/

lemma TargetProfile.mul {φ ψ : ℝ[X]} {a b c : ℝ} (hφ : TargetProfile φ a)
    (hψ : TargetProfile ψ b) (hac : a ≤ c) (hbc : b ≤ c) (hc : φ.eval c = 0 ∨ ψ.eval c = 0) :
    TargetProfile (φ * ψ) c where
  eval_eq_zero := by rcases hc with h | h <;> simp [eval_mul, h]
  nonneg z hz hz1 := by
    rw [eval_mul]
    exact mul_nonneg (hφ.nonneg z (hac.trans hz) hz1) (hψ.nonneg z (hbc.trans hz) hz1)
  deriv_nonneg z hz hz1 := by
    rw [derivative_mul, eval_add, eval_mul, eval_mul]
    have := hφ.nonneg z (hac.trans hz) hz1
    have := hψ.nonneg z (hbc.trans hz) hz1
    have := hφ.deriv_nonneg z (hac.trans hz) hz1
    have := hψ.deriv_nonneg z (hbc.trans hz) hz1
    positivity
  deriv2_nonneg z hz hz1 := by
    simp only [derivative_mul, derivative_add, eval_add, eval_mul]
    have := hφ.nonneg z (hac.trans hz) hz1
    have := hψ.nonneg z (hbc.trans hz) hz1
    have := hφ.deriv_nonneg z (hac.trans hz) hz1
    have := hψ.deriv_nonneg z (hbc.trans hz) hz1
    have := hφ.deriv2_nonneg z (hac.trans hz) hz1
    have := hψ.deriv2_nonneg z (hbc.trans hz) hz1
    positivity

/-- The star profile: `pⁿ` on `[0,1]`. -/
lemma targetProfile_pow {n : ℕ} (hn : 1 ≤ n) : TargetProfile ((X : ℝ[X]) ^ n) 0 where
  eval_eq_zero := by simp [zero_pow (by omega : n ≠ 0)]
  nonneg z hz _ := by simp only [eval_pow, eval_X]; positivity
  deriv_nonneg z hz _ := by
    simp only [derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X]; positivity
  deriv2_nonneg z hz _ := by
    rw [derivative_X_pow, derivative_C_mul_X_pow]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    positivity

/-! ### The induction -/

/-- What the induction proves for each generated graph. -/
def TPClaim {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  SatisfiesLowerBound G ∧
    ∀ (P : ℝ[X]) (r : ℕ), IsChromaticPolynomial G P → IsChromaticNumber G r →
      2 ≤ r → TargetProfile (targetPoly n P) (threshold r)

lemma tpClaim_of_edgeless {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset = ∅) : TPClaim G := by
  refine ⟨satisfiesLowerBound_of_edgeless G hE, fun P r _ hr hr2 ↦ ?_⟩
  have := (edgeFinset_eq_empty_iff_chromaticNumber_le_one hr).mp hE
  omega

/-- Transport of the claim between two decidability instances. -/
lemma tpClaim_congr {n : ℕ} (G : SimpleGraph (Fin n)) (i j : DecidableRel G.Adj)
    (h : @TPClaim n G i) : @TPClaim n G j := by
  have : i = j := Subsingleton.elim _ _
  subst this
  exact h

lemma tpClaim_union {m n : ℕ} (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hG : TPClaim G) (hH : TPClaim H) :
    TPClaim (disjointUnion G H) := by
  obtain ⟨P₁, hP₁⟩ := exists_isChromaticPolynomial G
  obtain ⟨P₂, hP₂⟩ := exists_isChromaticPolynomial H
  obtain ⟨r₁, hr₁⟩ := exists_isChromaticNumber G
  obtain ⟨r₂, hr₂⟩ := exists_isChromaticNumber H
  -- the per-component bound on the union's admissible interval
  have hcomp : ∀ {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] {Q : ℝ[X]} {s : ℕ},
      TPClaim F → IsChromaticPolynomial F Q → IsChromaticNumber F s → s ≤ max r₁ r₂ →
      ∀ {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
        (W : Graphon Ω ν), admissibleDensity (max r₁ r₂) (edgeDensity W) →
        0 ≤ chromaticTarget (V := Fin k) Q (edgeDensity W) ∧
          chromaticTarget (V := Fin k) Q (edgeDensity W) ≤ homDensity F W := by
    intro k F _ Q s hF hQ hs hsr Ω _ ν _ W hW
    by_cases hs2 : 2 ≤ s
    · have hprof := hF.2 Q s hQ hs hs2
      have hadm : admissibleDensity s (edgeDensity W) :=
        (threshold_mono hs2 hsr).trans hW
      refine ⟨?_, hF.1 Q s hQ hs W hadm⟩
      rw [chromaticTarget_eq_eval_targetPoly hQ]
      simp only [Fintype.card_fin]
      exact hprof.nonneg _ hadm (cliqueDensity_le_one 2 W)
    · have hE := (edgeFinset_eq_empty_iff_chromaticNumber_le_one hs).mpr (by omega)
      rw [chromaticTarget_of_edgeless F hE hQ, homDensity_of_edgeFinset_eq_empty F hE]
      exact ⟨zero_le_one, le_rfl⟩
  refine ⟨?_, ?_⟩
  · exact satisfiesLowerBound_disjointUnion G H hP₁ hr₁ hP₂ hr₂
      (fun W hW ↦ hcomp G hG hP₁ hr₁ (le_max_left _ _) W hW)
      (fun W hW ↦ hcomp H hH hP₂ hr₂ (le_max_right _ _) W hW)
  · intro P r hP hr hr2
    have hPeq : P = P₁ * P₂ := IsChromaticPolynomial.unique _ hP
      (isChromaticPolynomial_disjointUnion G H hP₁ hP₂)
    have hreq : r = max r₁ r₂ := IsChromaticNumber.unique _ hr
      (isChromaticNumber_disjointUnion G H hr₁ hr₂)
    subst hPeq hreq
    have hd₁ : P₁.natDegree ≤ m := by simpa using hP₁.natDegree_le
    have hd₂ : P₂.natDegree ≤ n := by simpa using hP₂.natDegree_le
    have hc₁ : P₁.coeff m = 1 := by simpa using hP₁.coeff_card
    have hc₂ : P₂.coeff n = 1 := by simpa using hP₂.coeff_card
    rw [targetPoly_mul hd₁ hd₂ hc₁ hc₂]
    by_cases h₁ : 2 ≤ r₁ <;> by_cases h₂ : 2 ≤ r₂
    · have p₁ := hG.2 P₁ r₁ hP₁ hr₁ h₁
      have p₂ := hH.2 P₂ r₂ hP₂ hr₂ h₂
      refine p₁.mul p₂ (threshold_mono h₁ (le_max_left _ _))
        (threshold_mono h₂ (le_max_right _ _)) ?_
      rcases le_total r₁ r₂ with h | h
      · right; rw [max_eq_right h]; exact p₂.eval_eq_zero
      · left; rw [max_eq_left h]; exact p₁.eval_eq_zero
    · have hE := (edgeFinset_eq_empty_iff_chromaticNumber_le_one hr₂).mpr (by omega)
      have ht := targetPoly_of_edgeless H hE hP₂
      simp only [Fintype.card_fin] at ht
      rw [ht, mul_one, max_eq_left (by omega)]
      exact hG.2 P₁ r₁ hP₁ hr₁ h₁
    · have hE := (edgeFinset_eq_empty_iff_chromaticNumber_le_one hr₁).mpr (by omega)
      have ht := targetPoly_of_edgeless G hE hP₁
      simp only [Fintype.card_fin] at ht
      rw [ht, one_mul, max_eq_right (by omega)]
      exact hH.2 P₂ r₂ hP₂ hr₂ h₂
    · omega

/-- The star `K_{1,n}` satisfies the claim. -/
lemma tpClaim_star (n : ℕ) (hn : 1 ≤ n) [DecidableRel (coneGraph (⊥ : SimpleGraph (Fin n))).Adj] :
    TPClaim (coneGraph (⊥ : SimpleGraph (Fin n))) := by
  have hbot : IsChromaticPolynomial (⊥ : SimpleGraph (Fin n)) (X ^ n) := by
    simpa using isChromaticPolynomial_of_edgeless (⊥ : SimpleGraph (Fin n)) (by simp)
  have hcone := isChromaticPolynomial_coneGraph (⊥ : SimpleGraph (Fin n)) hbot
  -- the target polynomial of the star is `Xⁿ`
  have hφ : targetPoly (n + 1) (X * (X ^ n).comp (X - 1)) = X ^ n := by
    apply Polynomial.funext
    intro z
    have h := chromaticTarget_eq_eval_targetPoly hcone z
    simp only [Fintype.card_fin] at h
    rw [← h]
    by_cases hz : z = 1
    · subst hz; simp
    · rw [chromaticTarget_of_ne_one _ hz, Fintype.card_fin]
      have hq : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
      simp only [eval_mul, eval_X, eval_comp, eval_pow, eval_sub, eval_one]
      have : 1 / (1 - z) - 1 = z / (1 - z) := by field_simp; ring
      rw [this, div_pow, pow_succ]
      field_simp
  have hr : IsChromaticNumber (coneGraph (⊥ : SimpleGraph (Fin n))) 2 := by
    have h1 : IsChromaticNumber (⊥ : SimpleGraph (Fin n)) 1 := by
      obtain ⟨r, hr⟩ := exists_isChromaticNumber (⊥ : SimpleGraph (Fin n))
      have hle := (edgeFinset_eq_empty_iff_chromaticNumber_le_one hr).mp (by simp)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
      · exfalso
        subst h
        have := hr.positive
        rw [properAssignmentCount, Finset.card_pos] at this
        obtain ⟨x, -⟩ := this
        exact (x ⟨0, hn⟩).elim0
      · rwa [h] at hr
    exact isChromaticNumber_coneGraph _ h1
  refine ⟨?_, ?_⟩
  · intro P r hP hr' Ω _ μ _ W hW
    have hPeq := IsChromaticPolynomial.unique _ hP hcone
    subst hPeq
    rw [chromaticTarget_eq_eval_targetPoly hcone]
    simp only [Fintype.card_fin]
    rw [hφ, eval_pow, eval_X]
    have hst : homDensity (coneGraph (⊥ : SimpleGraph (Fin n))) W = moment W n := by
      convert homDensity_starTree W n
    rw [hst]
    exact RootedTriangleTree.pow_le_moment W n
  · intro P r hP hr' hr2
    have hPeq := IsChromaticPolynomial.unique _ hP hcone
    have hreq := IsChromaticNumber.unique _ hr' hr
    subst hPeq hreq
    rw [hφ, show threshold 2 = 0 by norm_num [threshold]]
    exact targetProfile_pow hn

lemma tpClaim_cone {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (hn : 1 ≤ n)
    (hF : TPClaim F) : TPClaim (coneGraph F) := by
  obtain ⟨P, hP⟩ := exists_isChromaticPolynomial F
  obtain ⟨r, hr⟩ := exists_isChromaticNumber F
  by_cases hr2 : 2 ≤ r
  · -- `F` has an edge, hence at least two vertices
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : Subsingleton (Fin n) := by
        rw [Fin.subsingleton_iff_le_one]; omega
      have hE : F.edgeFinset = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        induction e using Sym2.inductionOn with
        | _ u v =>
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
          exact he.ne (Subsingleton.elim u v)
      have := (edgeFinset_eq_empty_iff_chromaticNumber_le_one hr).mp hE
      omega
    obtain ⟨h, rfl⟩ : ∃ h, n = h + 2 := ⟨n - 2, by omega⟩
    have hprof := hF.2 P r hP hr hr2
    have hbase : SatisfiesLowerBoundOn F (Set.Ioi (threshold r)) :=
      ((satisfiesLowerBound_iff_on hr).mp hF.1).mono fun p hp ↦ by
        show admissibleDensity r p
        exact le_of_lt hp
    obtain ⟨hbound, hprof'⟩ := lifting_aux F hP (threshold_lt_one hr2)
      hprof hbase
    rw [lift_threshold hr2] at hbound hprof'
    have hcone := isChromaticPolynomial_coneGraph F hP
    have hrc := isChromaticNumber_coneGraph F hr
    refine ⟨(satisfiesLowerBound_iff_on hrc).mpr hbound, fun Q s hQ hs _ ↦ ?_⟩
    have hQeq := IsChromaticPolynomial.unique _ hQ hcone
    have hseq := IsChromaticNumber.unique _ hs hrc
    subst hQeq hseq
    exact hprof'
  · -- `F` is edgeless: the cone is a star
    have hE := (edgeFinset_eq_empty_iff_chromaticNumber_le_one hr).mpr (by omega)
    have hbot : F = ⊥ := SimpleGraph.edgeFinset_eq_empty.mp hE
    subst hbot
    exact tpClaim_star n hn

/-- Generated graphs have at least one vertex. -/
lemma TPGenerated.one_le {n : ℕ} {G : SimpleGraph (Fin n)} (hG : TPGenerated G) : 1 ≤ n := by
  induction hG with
  | single => exact le_rfl
  | union _ _ ih₁ _ => omega
  | cone _ _ => omega

/-- **The induction of Theorem 1.3.** -/
theorem tpGenerated_claim {n : ℕ} {G : SimpleGraph (Fin n)} (hG : TPGenerated G) :
    ∀ [DecidableRel G.Adj], TPClaim G := by
  classical
  induction hG with
  | single =>
      intro _
      exact tpClaim_of_edgeless _ (by simp)
  | @union m n G H hG hH ihG ihH =>
      intro inst
      have h := @tpClaim_union m n G H (Classical.decRel _) (Classical.decRel _)
        (@ihG (Classical.decRel _)) (@ihH (Classical.decRel _))
      exact tpClaim_congr _ _ _ h
  | @cone n G hG ih =>
      intro inst
      have h := @tpClaim_cone n G (Classical.decRel _) hG.one_le (@ih (Classical.decRel _))
      exact tpClaim_congr _ _ _ h

/-- **Theorem 1.3: every trivially perfect graph satisfies the
Goodman-type lower bound** (the paper assumes at least one edge; edgeless graphs
are included here, both sides being `1`). -/
theorem IsTriviallyPerfect.satisfiesLowerBound {H : SimpleGraph V} [DecidableRel H.Adj]
    (hH : IsTriviallyPerfect H) : SatisfiesLowerBound H := by
  classical
  obtain ⟨n, G, hG, ⟨φ⟩⟩ := hH
  exact SatisfiesLowerBound.of_iso φ (tpGenerated_claim hG).1

end Taeyoung.Paper
