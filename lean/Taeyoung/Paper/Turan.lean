import Taeyoung.Paper.Basic
import Taeyoung.Methods.Negative.Chromatic

/-!
# Turán values and optimality at Turán densities (`paper.pdf`, Section 1)

The introduction records the first two facts below; the third is a Lean-side
complement that the paper does not state.

* (1.3): `t(K₂,T_k) = 1 - 1/k` and
  `t(H,T_k) = P_H(k)/k^{v(H)} = Φ_H(1 - 1/k)`
  (`homDensity_turan_eq_chromaticTarget`).
* (1.4) defines optimality of `T_k` (`TuranOptimal`); the paper notes
  right after it that if `H` satisfies the Goodman-type lower bound, then `T_k`
  is optimal at density `1 - 1/k` for every integer `k ≥ χ(H)`
  (`turanOptimal_of_satisfiesLowerBound`).  For a graph with an edge this is the
  bound at `p = 1 - 1/k > p̲_H`; an edgeless graph has `t(H,W) = 1` throughout.
* For densities `p ≥ 1 - 1/k` the same lower bound `t(H,W) ≥ t(H,T_k)` follows
  by scaling `W` down to `((1-1/k)/p)·W` and monotonicity
  (`TuranOptimal.le_of_le_edgeDensity`).

Edgeless graphs satisfy `SatisfiesLowerBound` (`satisfiesLowerBound_of_edgeless`),
since both sides are `1`; the paper defines the bound only for `χ(H) ≥ 2`
(before (1.2)).
-/

open MeasureTheory Polynomial

namespace Taeyoung.Paper

open Taeyoung Taeyoung.Methods.PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Every finite graph has a chromatic polynomial and a chromatic number -/

/-- Some polynomial satisfies the chromatic specification. -/
theorem exists_isChromaticPolynomial (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∃ P : Polynomial ℝ, IsChromaticPolynomial H P :=
  ⟨_, Methods.Negative.isChromaticPolynomial_of_surjCount H⟩

/-- A colouring with `|V|` colours always exists. -/
lemma properAssignmentCount_card_pos (H : SimpleGraph V) [DecidableRel H.Adj] :
    0 < properAssignmentCount H (Fintype.card V) := by
  classical
  rw [properAssignmentCount, Finset.card_pos]
  refine ⟨fun v ↦ Fintype.equivFin V v, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, fun u v huv he ↦ huv.ne ((Fintype.equivFin V).injective he)⟩

/-- Some natural number satisfies the chromatic-number specification. -/
theorem exists_isChromaticNumber (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∃ r : ℕ, IsChromaticNumber H r := by
  classical
  have hex : ∃ r, 0 < properAssignmentCount H r :=
    ⟨_, properAssignmentCount_card_pos H⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun k hk ↦ ?_⟩
  have := Nat.find_min hex hk
  omega

/-! ### Edgeless graphs -/

/-- With no edges the weight is identically one. -/
lemma homDensity_of_edgeFinset_eq_empty {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hE : H.edgeFinset = ∅)
    (W : Graphon Ω μ) : homDensity H W = 1 := by
  simp [homDensity, graphWeight, hE]

/-- A chromatic number at most one forces the graph to be edgeless. -/
lemma edgeFinset_eq_empty_of_chromaticNumber_le_one
    {H : SimpleGraph V} [DecidableRel H.Adj] {r : ℕ}
    (hr : IsChromaticNumber H r) (hr1 : r ≤ 1) : H.edgeFinset = ∅ := by
  classical
  have hpos := hr.positive
  rw [properAssignmentCount, Finset.card_pos] at hpos
  obtain ⟨x, hx⟩ := hpos
  rw [Finset.mem_filter] at hx
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    apply hx.2 he
    have : Subsingleton (Fin r) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr1 with h | h <;> subst h <;>
        infer_instance
    exact Subsingleton.elim _ _

/-- **Edgeless graphs satisfy the Goodman-type lower bound.**  The chromatic
polynomial is `x^{v(H)}`, so `Φ_H ≡ 1`, while `t(H,W) = 1` for every graphon. -/
theorem satisfiesLowerBound_of_edgeless (H : SimpleGraph V) [DecidableRel H.Adj]
    (hE : H.edgeFinset = ∅) : SatisfiesLowerBound H := by
  intro P r hP hr Ω _ μ _ W hadm
  rw [homDensity_of_edgeFinset_eq_empty H hE]
  have hp1 : edgeDensity W ≤ 1 := cliqueDensity_le_one 2 W
  by_cases hone : edgeDensity W = 1
  · rw [hone, chromaticTarget_at_one]
  · rw [chromaticTarget_of_ne_one P hone]
    -- `P` agrees with `x ↦ x^{|V|}` on the naturals
    have hPeq : P = X ^ Fintype.card V := by
      apply IsChromaticPolynomial.unique H hP
      intro k
      have hall : properAssignmentCount H k = k ^ Fintype.card V := by
        classical
        rw [properAssignmentCount]
        have : (Finset.univ.filter (IsProperAssignment H : (V → Fin k) → Prop)) =
            Finset.univ := by
          apply Finset.filter_true_of_mem
          intro x _ u v huv
          exfalso
          have : s(u, v) ∈ H.edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset]; exact huv
          rw [hE] at this
          exact absurd this (Finset.notMem_empty _)
        rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
      rw [hall]
      simp
    subst hPeq
    have hq : 0 < 1 - edgeDensity W := by
      have := lt_of_le_of_ne hp1 hone
      linarith
    rw [eval_pow, eval_X, ← mul_pow, mul_one_div_cancel hq.ne', one_pow]

/-! ### The Turán values -/

/-- `Φ_H(1 - 1/k) = P_H(k)/k^{v(H)}`. -/
theorem chromaticTarget_turan {H : SimpleGraph V} [DecidableRel H.Adj]
    {P : Polynomial ℝ} (hP : IsChromaticPolynomial H P) (k : ℕ) [NeZero k] :
    chromaticTarget (V := V) P (1 - 1 / (k : ℝ)) =
      (properAssignmentCount H k : ℝ) / (k : ℝ) ^ Fintype.card V := by
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have hne : (1 : ℝ) - 1 / (k : ℝ) ≠ 1 := by
    intro h
    have : 1 / (k : ℝ) = 0 := by linarith
    exact (one_div_ne_zero hk) this
  rw [chromaticTarget_of_ne_one P hne]
  have h1 : (1 : ℝ) - (1 - 1 / (k : ℝ)) = 1 / (k : ℝ) := by ring
  rw [h1, one_div_one_div, hP k, div_pow, one_pow, one_div, inv_mul_eq_div]

/-- **(1.3)**: `t(H,T_k) = P_H(k)/k^{v(H)} = Φ_H(1 - 1/k)`. -/
theorem homDensity_turan_eq_chromaticTarget {H : SimpleGraph V} [DecidableRel H.Adj]
    {P : Polynomial ℝ} (hP : IsChromaticPolynomial H P) (k : ℕ) [NeZero k] :
    homDensity H (balancedMultipartiteGraphon k) =
      chromaticTarget (V := V) P (1 - 1 / (k : ℝ)) := by
  rw [homDensity_balancedMultipartite, chromaticTarget_turan hP]

/-- The edge density of `T_k` is `1 - 1/k`. -/
theorem edgeDensity_turan (k : ℕ) [NeZero k] :
    edgeDensity (balancedMultipartiteGraphon k) = 1 - 1 / (k : ℝ) :=
  edgeDensity_balancedMultipartite k

/-- Optimality of `T_k` is the Goodman-type inequality at the single density
`1 - 1/k`. -/
theorem turanOptimal_iff_satisfiesLowerBoundOn {H : SimpleGraph V}
    [DecidableRel H.Adj] (k : ℕ) [NeZero k] :
    TuranOptimal H k ↔ SatisfiesLowerBoundOn H {1 - 1 / (k : ℝ)} := by
  constructor
  · intro h P hP Ω _ μ _ W hW
    rw [Set.mem_singleton_iff] at hW
    rw [hW, ← homDensity_turan_eq_chromaticTarget hP]
    exact h W hW
  · intro h Ω _ μ _ W hW
    obtain ⟨P, hP⟩ := exists_isChromaticPolynomial H
    rw [homDensity_turan_eq_chromaticTarget hP k, ← hW]
    exact h P hP W (by rw [Set.mem_singleton_iff, hW])

/-- **(1.2) implies (1.4)**: a graph satisfying the
Goodman-type lower bound has `T_k` optimal for every `k ≥ χ(H)`. -/
theorem turanOptimal_of_satisfiesLowerBound {H : SimpleGraph V} [DecidableRel H.Adj]
    (hsat : SatisfiesLowerBound H) {r : ℕ} (hr : IsChromaticNumber H r)
    (k : ℕ) [NeZero k] (hk : r ≤ k) : TuranOptimal H k := by
  intro Ω _ μ _ W hW
  rcases le_or_gt r 1 with hr1 | hr2
  · have hE := edgeFinset_eq_empty_of_chromaticNumber_le_one hr hr1
    rw [homDensity_of_edgeFinset_eq_empty H hE, homDensity_of_edgeFinset_eq_empty H hE]
  · obtain ⟨P, hP⟩ := exists_isChromaticPolynomial H
    rw [homDensity_turan_eq_chromaticTarget hP k, ← hW]
    apply hsat P r hP hr W
    rw [admissibleDensity, hW]
    have hr1 : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ r - 1 by omega)
    have hkr : ((r - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (show r - 1 ≤ k by omega)
    have hpos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by linarith
    have : 1 / (k : ℝ) ≤ 1 / ((r - 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hpos hkr
    linarith

/-! ### Scaling a graphon down -/

/-- `c·W` for `0 ≤ c ≤ 1`. -/
def _root_.Taeyoung.Graphon.scale {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (W : Graphon Ω μ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : Graphon Ω μ where
  toFun x y := c * W x y
  measurable := measurable_const.mul W.measurable
  nonneg x y := mul_nonneg hc0 (W.nonneg x y)
  le_one x y := mul_le_one₀ hc1 (W.nonneg x y) (W.le_one x y)
  symm x y := by rw [W.symm x y]

lemma graphWeight_scale {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon Ω μ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : V → Ω) :
    graphWeight H (W.scale c hc0 hc1) x = c ^ H.edgeFinset.card * graphWeight H W x := by
  rw [graphWeight, graphWeight, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ ↦ ?_
  induction e using Sym2.inductionOn with
  | _ u v => rw [edgeValue_mk, edgeValue_mk]; rfl

/-- `t(H, c·W) = c^{e(H)}·t(H,W)`. -/
theorem homDensity_scale {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    homDensity H (W.scale c hc0 hc1) = c ^ H.edgeFinset.card * homDensity H W := by
  rw [homDensity, homDensity]
  simp_rw [graphWeight_scale H W hc0 hc1]
  exact integral_const_mul _ _

lemma edgeFinset_top_two_card : (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1 := by
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

theorem edgeDensity_scale {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (W : Graphon Ω μ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    edgeDensity (W.scale c hc0 hc1) = c * edgeDensity W := by
  rw [edgeDensity, cliqueDensity, homDensity_scale, edgeFinset_top_two_card, pow_one]
  rfl

/-- **Optimality propagates upward in density.**  If `T_k` is optimal at its own
density, then `t(H,W) ≥ t(H,T_k)` for every graphon of edge density
`p ≥ 1 - 1/k`: scale `W` by `(1-1/k)/p` and use `t(H,cW) = c^{e(H)} t(H,W)`. -/
theorem TuranOptimal.le_of_le_edgeDensity {H : SimpleGraph V} [DecidableRel H.Adj]
    {k : ℕ} [NeZero k] (hopt : TuranOptimal H k)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (hp : 1 - 1 / (k : ℝ) ≤ edgeDensity W) :
    homDensity H (balancedMultipartiteGraphon k) ≤ homDensity H W := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have ha0 : (0 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hk1
    linarith
  set p := edgeDensity W with hpdef
  set c : ℝ := (1 - 1 / (k : ℝ)) / p with hcdef
  rcases eq_or_lt_of_le (le_trans ha0 hp) with hp0 | hppos
  · -- `p = 0`, hence `1 - 1/k = 0`, and the scaled graphon is `0·W`
    have ha : 1 - 1 / (k : ℝ) = 0 := le_antisymm (hp0 ▸ hp) ha0
    have hW0 : edgeDensity (W.scale 0 le_rfl zero_le_one) = 1 - 1 / (k : ℝ) := by
      rw [edgeDensity_scale, zero_mul, ha]
    have h := hopt (W.scale 0 le_rfl zero_le_one) hW0
    rw [homDensity_scale] at h
    calc homDensity H (balancedMultipartiteGraphon k)
        ≤ 0 ^ H.edgeFinset.card * homDensity H W := h
      _ ≤ homDensity H W := by
        rcases Nat.eq_zero_or_pos H.edgeFinset.card with he | he
        · rw [he, pow_zero, one_mul]
        · rw [zero_pow he.ne', zero_mul]; exact homDensity_nonneg H W
  · have hc0 : 0 ≤ c := div_nonneg ha0 hppos.le
    have hc1 : c ≤ 1 := by rw [hcdef, div_le_one hppos]; exact hp
    have hW' : edgeDensity (W.scale c hc0 hc1) = 1 - 1 / (k : ℝ) := by
      rw [edgeDensity_scale, ← hpdef, hcdef, div_mul_cancel₀ _ hppos.ne']
    have h := hopt (W.scale c hc0 hc1) hW'
    rw [homDensity_scale] at h
    calc homDensity H (balancedMultipartiteGraphon k)
        ≤ c ^ H.edgeFinset.card * homDensity H W := h
      _ ≤ 1 * homDensity H W :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hc0 hc1) (homDensity_nonneg H W)
      _ = homDensity H W := one_mul _

end Taeyoung.Paper
