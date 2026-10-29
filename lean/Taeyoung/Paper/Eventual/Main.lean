import Taeyoung.Paper.Eventual.Spectral
import Taeyoung.Paper.Eventual.TruncD
import Taeyoung.Paper.Eventual.Local
import Taeyoung.Paper.Eventual.EvenGirth

/-!
# Eventual validity and girth (`paper.pdf`, Theorem 1.6)

Let `H` be a finite simple graph containing a cycle (e.g. a nonbipartite graph), and
`n = v(H)`. The following are equivalent:

1. for all sufficiently large `k`, `T_k` minimizes `t(H,W)` among graphons of edge density
   `1 - 1/k` (`TuranOptimal H k`);
2. `H` satisfies the Goodman-type lower bound at all sufficiently high densities
   (`EventuallySatisfiesLowerBound H`);
3. the girth of `H` is odd.

If the girth is odd, `t(H,W) ≥ Φ_H(p)` for every graphon of edge density
`p > 1 - 1/(72 n^{12})` (`satisfiesLowerBoundOn_threshold`), and `T_k` is optimal for every
`k > 72 n^{12}` (`turanOptimal_of_odd_girth`).

Assembly, following the paper:

* `local_of_small_degree`: Proposition 4.12 with `Δ = (6n⁶)⁻¹`:
  `Γ_H(K) ≥ 0` whenever `d_K ≤ (6n⁶)⁻¹` (from `local_estimate`, with the hypothesis for
  girth `≥ 5` supplied by `cycle_comparison`, whose constant
  `((s-2)(s-3))/((g-2)(g-3))` is at most `n²/6`);
* `satisfiesLowerBoundOn_threshold`: the polynomial threshold (1.7)
  (Proposition 4.15, i.e. `truncation`, with `U = 1 - W`);
* `eventual_tfae`: the equivalence, with `not_turanOptimal_of_even_girth` for even girth
  (Proposition 4.17).
-/

open MeasureTheory Finset SimpleGraph Polynomial

namespace Taeyoung.Paper.Eventual

open Taeyoung Taeyoung.Methods.PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

section Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma compl_compl (W : Graphon Ω μ) : W.compl.compl = W := by
  obtain ⟨f, h1, h2, h3, h4⟩ := W
  unfold Graphon.compl
  congr 1
  funext x y
  show 1 - (1 - f x y) = f x y
  ring

/-- The constant of the cycle comparison is at most `n²/6` for `5 ≤ g ≤ s ≤ n`. -/
lemma cmpConst_le {p r n : ℕ} (hp : 1 ≤ p) (hn : p + r + 4 ≤ n) :
    cmpConst p r ≤ (n : ℝ) ^ 2 / 6 := by
  unfold cmpConst
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hn' : ((p + r : ℕ) : ℝ) + 2 ≤ n := by
    have : ((p + r + 4 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this ⊢
    linarith
  have hpr : (0 : ℝ) ≤ ((p + r : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h6 : (6 : ℝ) ≤ ((p : ℝ) + 2) * ((p : ℝ) + 1) := by nlinarith
  have hsq : (((p + r : ℕ) : ℝ) + 2) * (((p + r : ℕ) : ℝ) + 1) ≤ (n : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- The hypothesis `hspec` of `local_estimate`, from `cycle_comparison`. -/
lemma hspec_of_comparison (hodd : Odd H.girth) (U : Graphon Ω μ) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hdeg : ∀ x, degree U x ≤ Δ) :
    5 ≤ H.girth →
      (∀ s, H.girth < s → s ≤ Fintype.card V →
        Ss U s ≤ (Fintype.card V : ℝ) ^ 2 / 6 * Δ ^ (s - H.girth) * Ss U H.girth) ∧
      0 ≤ Ss U H.girth := by
  intro h5
  obtain ⟨p, hgp⟩ : ∃ p, H.girth = p + 4 := ⟨H.girth - 4, by omega⟩
  have hp : Odd p := by
    rw [hgp] at hodd
    exact (Nat.odd_add.mp hodd).mpr (by decide)
  have hp1 : 1 ≤ p := by
    obtain ⟨j, hj⟩ := hp; omega
  have hc := cycle_comparison hΔ hdeg hp
  rw [hgp]
  refine ⟨fun s hs hsn ↦ ?_, (hc 0).1⟩
  obtain ⟨r, rfl⟩ : ∃ r, s = p + r + 4 := ⟨s - (p + 4), by omega⟩
  have hsub : p + r + 4 - (p + 4) = r := by omega
  rw [hsub]
  have hS0 := (hc r).1
  have h1 := (hc r).2
  have hk := cmpConst_le (r := r) hp1 hsn
  have hnn : 0 ≤ Δ ^ r * Ss U (p + 4) := mul_nonneg (pow_nonneg hΔ r) hS0
  calc Ss U (p + r + 4) ≤ cmpConst p r * Δ ^ r * Ss U (p + 4) := h1
    _ = cmpConst p r * (Δ ^ r * Ss U (p + 4)) := by ring
    _ ≤ (Fintype.card V : ℝ) ^ 2 / 6 * (Δ ^ r * Ss U (p + 4)) :=
        mul_le_mul_of_nonneg_right hk hnn
    _ = _ := by ring

lemma card_pos_of_odd_girth (hodd : Odd H.girth) : 0 < Fintype.card V := by
  have hcyc : ¬ H.IsAcyclic := fun h ↦ by
    rw [← SimpleGraph.girth_eq_zero] at h
    rw [h] at hodd
    exact Nat.not_odd_zero hodd
  have h3 := H.three_le_girth hcyc
  have := girth_le_card hcyc
  omega

/-- **Proposition 4.12** with `Δ = (6n⁶)⁻¹`: if every degree of `K` is
at most `(6n⁶)⁻¹`, then `Γ_H(K) = t(H,1-K) - Ψ_H(q(K)) ≥ 0`. -/
theorem local_of_small_degree (hodd : Odd H.girth) {P : ℝ[X]} (hP : IsChromaticPolynomial H P)
    (K : Graphon Ω μ) (hK : ∀ x, degree K x ≤ 1 / (6 * (Fintype.card V : ℝ) ^ 6)) :
    0 ≤ gammaFun H P K := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast card_pos_of_odd_girth hodd
  have hΔ : (0 : ℝ) < 1 / (6 * (Fintype.card V : ℝ) ^ 6) := by positivity
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := hn.ne'
  have hΔn : (Fintype.card V : ℝ) ^ 6 * (1 / (6 * (Fintype.card V : ℝ) ^ 6)) ≤ 1 / 6 :=
    le_of_eq (by field_simp)
  have h := local_estimate hodd hP K.compl hΔ (by rw [compl_compl]; exact hK) hΔn
    (by rw [compl_compl]; exact hspec_of_comparison hodd K hΔ.le hK)
  rw [edgeDensity_compl] at h
  unfold gammaFun
  linarith

/-- **The polynomial threshold in Theorem 1.6**: for odd girth,
`t(H,W) ≥ Φ_H(p)` for every graphon of edge density `p > 1 - 1/(72 n^{12})`. -/
theorem satisfiesLowerBoundOn_threshold (hodd : Odd H.girth) :
    SatisfiesLowerBoundOn H (Set.Ioi (1 - 1 / (72 * (Fintype.card V : ℝ) ^ 12))) := by
  intro P hP Ω _ μ _ W hW
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast card_pos_of_odd_girth hodd
  have hq : meanDeg W.compl < (1 / (6 * (Fintype.card V : ℝ) ^ 6)) ^ 2 / 2 := by
    rw [meanDeg_compl]
    have he : (1 / (6 * (Fintype.card V : ℝ) ^ 6)) ^ 2 / 2 =
        1 / (72 * (Fintype.card V : ℝ) ^ 12) := by
      field_simp; ring
    rw [he]
    have := Set.mem_Ioi.mp hW
    linarith
  have h := truncation hodd hP W.compl (fun K hK ↦ local_of_small_degree hodd hP K hK) hq
  unfold gammaFun at h
  rw [compl_compl, meanDeg_compl, sub_sub_cancel] at h
  linarith

end Graphons

/-- **Theorem 1.6, the Turán cutoff**: for odd girth, `T_k` is optimal for every
`k > 72 n^{12}`. -/
theorem turanOptimal_of_odd_girth (hodd : Odd H.girth) (k : ℕ) [NeZero k]
    (hk : 72 * Fintype.card V ^ 12 < k) : TuranOptimal H k := by
  rw [turanOptimal_iff_satisfiesLowerBoundOn]
  refine (satisfiesLowerBoundOn_threshold hodd).mono ?_
  intro p hp
  rw [Set.mem_singleton_iff] at hp
  rw [hp, Set.mem_Ioi]
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast card_pos_of_odd_girth hodd
  have hk' : (72 * (Fintype.card V : ℝ) ^ 12) < k := by exact_mod_cast hk
  have : 1 / (k : ℝ) < 1 / (72 * (Fintype.card V : ℝ) ^ 12) :=
    one_div_lt_one_div_of_lt (by positivity) hk'
  linarith

/-- Validity at high densities gives optimality of `T_k` for all large `k`
(1.3). -/
theorem eventually_turanOptimal_of_eventually (h : EventuallySatisfiesLowerBound H) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ [NeZero k], TuranOptimal H k := by
  obtain ⟨pH, hpH, hS⟩ := h
  refine ⟨⌈1 / (1 - pH)⌉₊ + 1, fun k hk _ ↦ ?_⟩
  rw [turanOptimal_iff_satisfiesLowerBoundOn]
  refine hS.mono ?_
  intro p hp
  rw [Set.mem_singleton_iff] at hp
  rw [hp, Set.mem_Ioi]
  have h1 : (0 : ℝ) < 1 - pH := by linarith
  have h2 : 1 / (1 - pH) < k := by
    have := Nat.le_ceil (1 / (1 - pH))
    have hk' : ((⌈1 / (1 - pH)⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at hk'
    linarith
  have h3 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) h2
  have h4 : 1 / (k : ℝ) < 1 - pH := by
    rw [div_lt_iff₀ h3]
    rw [div_lt_iff₀ h1] at h2
    linarith
  linarith

/-- **Theorem 1.6.** For a graph `H` containing a cycle (in particular, for a
nonbipartite graph), the following are equivalent:
(i) `T_k` is optimal for all sufficiently large `k`;
(ii) `H` satisfies the Goodman-type lower bound at all sufficiently high densities;
(iii) the girth of `H` is odd. -/
theorem eventual_tfae (hcyc : ¬ H.IsAcyclic) :
    [∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ [NeZero k], TuranOptimal H k,
      EventuallySatisfiesLowerBound H,
      Odd H.girth].TFAE := by
  tfae_have 3 → 2 := fun hodd ↦ ⟨_, by
    have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast card_pos_of_odd_girth hodd
    have : (0 : ℝ) < 1 / (72 * (Fintype.card V : ℝ) ^ 12) := by positivity
    linarith, satisfiesLowerBoundOn_threshold hodd⟩
  tfae_have 2 → 1 := eventually_turanOptimal_of_eventually
  tfae_have 1 → 3 := by
    rintro ⟨k₀, hk₀⟩
    by_contra hodd
    have heven : Even H.girth := Nat.not_odd_iff_even.mp hodd
    set k := max k₀ (H.edgeFinset.card + 2 ^ H.edgeFinset.card + 1) with hkdef
    have hlt : H.edgeFinset.card + 2 ^ H.edgeFinset.card < k :=
      lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    haveI : NeZero k := ⟨Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hlt)⟩
    exact not_turanOptimal_of_even_girth H hcyc heven k hlt (hk₀ k (le_max_left _ _))
  tfae_finish

/-- **Theorem 1.6** for nonbipartite graphs, as stated in the paper. -/
theorem eventual_tfae_of_not_bipartite (hH : ¬ H.IsBipartite) :
    [∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ [NeZero k], TuranOptimal H k,
      EventuallySatisfiesLowerBound H,
      Odd H.girth].TFAE :=
  eventual_tfae fun h ↦ hH h.isBipartite

end Taeyoung.Paper.Eventual
