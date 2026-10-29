import Taeyoung.Paper.Eventual.LocalPrelim

/-!
# The polynomial local estimate (`paper.pdf`, Proposition 4.12)

Let `H` have odd girth `g`, `n` vertices and `m` edges, let `W` be a graphon,
`U = 1 - W`, and suppose the degree function of `U` is at most `Δ`, with
`n⁶ Δ ≤ 1/6`.  Then `t(H,W) ≥ Φ_H(p)` (`local_estimate`).  This is the final assertion of
the proposition; the quantitative bound (4.26) (under `mΔ, nΔ ≤ 1/2`)
is not stated separately.

The forest expansion splits `t(H,W) - Φ_H(p)` into

* the open forests: `≥ (1 - m³Δ) X` (`term1_ge`), the two-edge forests giving
  `aX` with `a ≥ 1` and the larger ones the error `E_X ≤ m³ΔX` (the paper's
  (4.28) has `2m³ΔX`);
* the closed forests: `≥ c_g Q_g - ∑_s c_s w_s Q_s` with `w_s = (1+Δ)^m - [s = g]`
  (`term2_ge`; cf. (4.29)).

For `g = 3` the cycle terms are controlled by Lemma 4.6; for
`g ≥ 5` by `S_s ≤ (n²/6) Δ^{s-g} S_g` and `S_g ≥ 0`, consequences of Theorem
4.7 (as `(g-2)(g-3) ≥ 6`, `(s-2)(s-3) ≤ n²`), which `local_estimate`
takes as the hypothesis `hspec` (discharged by `hspec_of_comparison` in `Main.lean`, from
`cycle_comparison` in `Spectral.lean`).
-/

open MeasureTheory Finset SimpleGraph Polynomial

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-! ### The open forests -/

/-- **The open forests contribute at least `(1 - m³Δ) X`.** -/
theorem term1_ge (hcyc : ¬ H.IsAcyclic) (U : Graphon Ω μ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hdeg : ∀ x, degree U x ≤ Δ) (hmΔ : (H.edgeFinset.card : ℝ) * Δ ≤ 1 / 2) :
    (1 - (H.edgeFinset.card : ℝ) ^ 3 * Δ) * degVar U ≤
      ∑ F ∈ openForests H.edgeFinset,
        (-1) ^ F.card * (forestDens U F - meanDeg U ^ F.card) := by
  classical
  set E := H.edgeFinset
  set O := openForests E
  set X := degVar U
  set q := meanDeg U
  have hX0 : 0 ≤ X := degVar_nonneg U
  set τ : Finset (Sym2 V) → ℝ := fun F ↦ (-1) ^ F.card * (forestDens U F - q ^ F.card)
  set lam : Finset (Sym2 V) → ℝ := fun F ↦
    if 3 ≤ F.card then -((F.card.choose 2 : ℝ) * Δ ^ (F.card - 2) * X) else 0
  have hOmem : ∀ F ∈ O, F ⊆ E ∧ IsForest F ∧ ∀ f ∈ F, ¬ f.IsDiag := by
    intro F hF
    obtain ⟨hFf, -⟩ := mem_openForests.mp hF
    obtain ⟨hFE, hfor⟩ := mem_forests.mp hFf
    exact ⟨hFE, hfor, fun f hf ↦ not_isDiag_of_mem_edgeFinset H f (hFE hf)⟩
  have htl : ∀ F ∈ O, lam F ≤ τ F := by
    intro F hF
    obtain ⟨-, hfor, hnd⟩ := hOmem F hF
    have hvar := forest_variance_unweighted U hΔ hdeg hfor hnd
    have hΔ2 : 0 < Δ ^ 2 := by positivity
    change Δ ^ 2 * |forestDens U F - q ^ F.card| ≤ _ at hvar
    by_cases h3 : 3 ≤ F.card
    · simp only [lam, τ, if_pos h3]
      have hpow : Δ ^ F.card = Δ ^ 2 * Δ ^ (F.card - 2) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow] at hvar
      have habs : |forestDens U F - q ^ F.card| ≤ (F.card.choose 2 : ℝ) * Δ ^ (F.card - 2) * X := by
        have : Δ ^ 2 * |forestDens U F - q ^ F.card| ≤
            Δ ^ 2 * ((F.card.choose 2 : ℝ) * Δ ^ (F.card - 2) * X) := by linarith
        exact le_of_mul_le_mul_left this hΔ2
      have h1 : -|forestDens U F - q ^ F.card| ≤ (-1) ^ F.card * (forestDens U F - q ^ F.card) := by
        rcases neg_one_pow_eq_or ℝ F.card with h | h <;> rw [h]
        · linarith [neg_abs_le (forestDens U F - q ^ F.card)]
        · linarith [le_abs_self (forestDens U F - q ^ F.card)]
      linarith
    · simp only [lam, τ, if_neg h3]
      by_cases h2 : F.card = 2
      · rw [h2]
        rcases forestDens_two U hnd h2 with ⟨-, ht⟩ | ⟨-, ht⟩
        · rw [ht, Mom_two_eq]; simp only [even_two, Even.neg_one_pow, one_mul]; linarith
        · rw [ht]; simp [q]
      · have hle : F.card ≤ 1 := by omega
        have hch : F.card.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hch] at hvar
        simp only [Nat.cast_zero, zero_mul] at hvar
        have : |forestDens U F - q ^ F.card| = 0 :=
          le_antisymm (le_of_mul_le_mul_left (by linarith) hΔ2) (abs_nonneg _)
        rw [abs_eq_zero.mp this, mul_zero]
  -- the adjacent pair
  obtain ⟨Fs, hFs, hcard, hadj⟩ := exists_adjacent_open hcyc
  have hτs : τ Fs = X := by
    obtain ⟨-, -, hnd⟩ := hOmem Fs hFs
    simp only [τ, hcard]
    rcases forestDens_two U hnd hcard with ⟨-, ht⟩ | ⟨hn, -⟩
    · rw [ht, Mom_two_eq]; simp only [even_two, Even.neg_one_pow, one_mul]; ring
    · exact absurd hadj hn
  have hls : lam Fs = 0 := by simp [lam, hcard]
  -- sum up
  have hlam_sum : ∑ F ∈ O, lam F ≥ -((E.card : ℝ) ^ 3 * Δ * X) := by
    have hsub : ∑ F ∈ O, -lam F ≤ ∑ F ∈ E.powerset, -lam F := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun F hF ↦ ?_) (fun F _ _ ↦ ?_)
      · exact Finset.mem_powerset.mpr (hOmem F hF).1
      · simp only [lam]; split_ifs
        · have := pow_nonneg hΔ.le (F.card - 2)
          have : (0 : ℝ) ≤ F.card.choose 2 := Nat.cast_nonneg _
          simp only [neg_neg]; positivity
        · simp
    have hpow : ∑ F ∈ E.powerset, -lam F = (∑ F ∈ E.powerset,
        (if 3 ≤ F.card then (F.card.choose 2 : ℝ) * Δ ^ (F.card - 2) else 0)) * X := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun F _ ↦ ?_
      simp only [lam]; split_ifs <;> ring
    have herr := sum_forest_error_le E hΔ.le hmΔ
    rw [Finset.sum_neg_distrib] at hsub
    have : (∑ F ∈ E.powerset, -lam F) ≤ (E.card : ℝ) ^ 3 * Δ * X := by
      rw [hpow]; exact mul_le_mul_of_nonneg_right herr hX0
    linarith
  have hsplit := Finset.add_sum_erase O τ hFs
  have hsplitl := Finset.add_sum_erase O lam hFs
  have hrest : ∑ F ∈ O.erase Fs, lam F ≤ ∑ F ∈ O.erase Fs, τ F :=
    Finset.sum_le_sum fun F hF ↦ htl F (Finset.mem_of_mem_erase hF)
  show (1 - (E.card : ℝ) ^ 3 * Δ) * X ≤ ∑ F ∈ O, τ F
  rw [← hsplit, hτs]
  rw [hls, zero_add] at hsplitl
  nlinarith

/-! ### The closed forests -/

/-- **The closed forests contribute at least `c_g Q_g - ∑_s c_s w_s Q_s`**, where
`w_s = (1+Δ)^m - [s = g]` (cf. (4.29)). -/
theorem term2_ge (hodd : Odd H.girth) (U : Graphon Ω μ) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hdeg : ∀ x, degree U x ≤ Δ) :
    ((cycleSets H H.girth).card : ℝ) * Qs U H.girth -
        ∑ s ∈ Finset.range (Fintype.card V + 1), ((cycleSets H s).card : ℝ) *
          ((1 + Δ) ^ H.edgeFinset.card - if s = H.girth then 1 else 0) * Qs U s ≤
      ∑ F ∈ (forests H.edgeFinset).filter (fun F ↦ closedEdges H.edgeFinset F ≠ ∅),
        (-1) ^ F.card * intervalInt H.edgeFinset U F := by
  classical
  set E := H.edgeFinset
  set T := (forests E).filter (fun F ↦ closedEdges E F ≠ ∅)
  set L := leadingForests H
  have hLT : L ⊆ T := by
    intro F hF
    obtain ⟨h1, h2, -⟩ := mem_leadingForests.mp hF
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
  have hL : ∑ F ∈ L, (-1) ^ F.card * intervalInt E U F = L.card * Qs U H.girth := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun F hF ↦ ?_
    obtain ⟨-, -, hcard⟩ := mem_leadingForests.mp hF
    have heven : Even F.card := by
      obtain ⟨r, hr⟩ := hodd; exact ⟨r, by omega⟩
    rw [heven.neg_one_pow, intervalInt_leading U hF]
    simp
  have hcL : ((cycleSets H H.girth).card : ℝ) * Qs U H.girth ≤ L.card * Qs U H.girth :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast card_cycleSets_le_card_leading)
      (Qs_nonneg U _)
  have hrest : -(∑ F ∈ (forests E).filter
        (fun F ↦ closedEdges E F ≠ ∅ ∧ H.girth ≤ F.card), intervalInt E U F) ≤
      ∑ F ∈ T \ L, (-1) ^ F.card * intervalInt E U F := by
    have h1 : ∑ F ∈ T \ L, intervalInt E U F ≤ ∑ F ∈ (forests E).filter
        (fun F ↦ closedEdges E F ≠ ∅ ∧ H.girth ≤ F.card), intervalInt E U F := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun F hF ↦ ?_)
        (fun F _ _ ↦ intervalInt_nonneg _ _ _)
      obtain ⟨hFT, hFL⟩ := Finset.mem_sdiff.mp hF
      obtain ⟨hFf, hB⟩ := Finset.mem_filter.mp hFT
      have hFE := (mem_forests.mp hFf).1
      have hg := girth_le_card_add_one hFE hB
      have hne : F.card + 1 ≠ H.girth := fun h ↦ hFL (mem_leadingForests.mpr ⟨hFf, hB, h⟩)
      exact Finset.mem_filter.mpr ⟨hFf, hB, by omega⟩
    have h2 : -(∑ F ∈ T \ L, intervalInt E U F) ≤ ∑ F ∈ T \ L,
        (-1) ^ F.card * intervalInt E U F := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun F _ ↦ ?_
      have hI := intervalInt_nonneg E U F
      rcases neg_one_pow_eq_or ℝ F.card with h | h <;> rw [h] <;> linarith
    linarith
  have hsum := sum_intervalInt_le (H := H) U hΔ0 hdeg
  rw [← Finset.sum_sdiff hLT, hL]
  linarith

/-! ### Splitting the cycle sum -/

lemma sum_range_split {f : ℕ → ℝ} {g n : ℕ} (hgn : g ≤ n) (hf : ∀ s < g, f s = 0) :
    ∑ s ∈ Finset.range (n + 1), f s = f g + ∑ j ∈ Finset.range (n - g), f (g + 1 + j) := by
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive f (Nat.zero_le g) (by omega : g ≤ n + 1),
    ← Finset.sum_Ico_consecutive f (Nat.le_succ g) (by omega : g + 1 ≤ n + 1)]
  have h0 : ∑ s ∈ Finset.Ico 0 g, f s = 0 :=
    Finset.sum_eq_zero fun s hs ↦ hf s (Finset.mem_Ico.mp hs).2
  rw [h0, zero_add, Nat.Ico_succ_singleton, Finset.sum_singleton, Finset.sum_Ico_eq_sum_range]
  congr 1
  rw [show n + 1 - (g + 1) = n - g by omega]

lemma two_choose_two_le (k n : ℕ) (h : k + 1 ≤ n) :
    2 * (((k + 1).choose 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h1 : 2 * (k + 1).choose 2 ≤ n ^ 2 := by
    rw [Nat.choose_two_right]
    calc 2 * ((k + 1) * (k + 1 - 1) / 2) ≤ (k + 1) * (k + 1 - 1) := by
          rw [mul_comm]; exact Nat.div_mul_le_self _ _
      _ ≤ n * n := Nat.mul_le_mul h (by omega)
      _ = n ^ 2 := (sq n).symm
  exact_mod_cast h1

/-! ### The local estimate -/

set_option maxHeartbeats 2000000 in
/-- **Proposition 4.12**, final assertion.  If the girth of `H` is odd, the
degree function of `1 - W` is at most `Δ`, and `n⁶ Δ ≤ 1/6`, then `t(H,W) ≥ Φ_H(p)`.
For girth at least `5` the hypothesis `hspec` is a consequence of the cycle comparison
(Theorem 4.7) together with `S_g ≥ 0`. -/
theorem local_estimate (hodd : Odd H.girth) {P : ℝ[X]} (hP : IsChromaticPolynomial H P)
    (W : Graphon Ω μ) {Δ : ℝ} (hΔ : 0 < Δ) (hdeg : ∀ x, degree W.compl x ≤ Δ)
    (hΔn : (Fintype.card V : ℝ) ^ 6 * Δ ≤ 1 / 6)
    (hspec : 5 ≤ H.girth →
      (∀ s, H.girth < s → s ≤ Fintype.card V →
        Ss W.compl s ≤ (Fintype.card V : ℝ) ^ 2 / 6 * Δ ^ (s - H.girth) * Ss W.compl H.girth) ∧
      0 ≤ Ss W.compl H.girth) :
    chromaticTarget (V := V) P (edgeDensity W) ≤ homDensity H W := by
  classical
  set U := W.compl with hU
  set g := H.girth with hg
  set n := Fintype.card V with hn
  set E := H.edgeFinset
  set m := E.card with hm
  set X := degVar U with hX
  have hcyc : ¬ H.IsAcyclic := by
    intro hac
    have h0 : g = 0 := by rw [hg]; exact girth_eq_zero.mpr hac
    rw [h0] at hodd
    exact absurd hodd (by decide)
  have hg3 : 3 ≤ g := H.three_le_girth hcyc
  have hgn : g ≤ n := girth_le_card hcyc
  set N : ℝ := (n : ℝ) with hN
  have hN3 : (3 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hg3.trans hgn
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hmn : (m : ℝ) ≤ N ^ 2 / 2 := card_edgeFinset_le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hX0 : 0 ≤ X := degVar_nonneg U
  -- numerical consequences of `n⁶ Δ ≤ 1/6`
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hN2 : N ^ 2 ≤ N ^ 6 := pow_le_pow_right₀ hN1' (by norm_num)
  have hN5 : N ^ 5 ≤ N ^ 6 := pow_le_pow_right₀ hN1' (by norm_num)
  have hN1 : N ≤ N ^ 6 := by
    calc N = N ^ 1 := (pow_one _).symm
      _ ≤ N ^ 6 := pow_le_pow_right₀ hN1' (by norm_num)
  have hN6 : (1 : ℝ) ≤ N ^ 6 := one_le_pow₀ hN1'
  have hNΔ : N * Δ ≤ N ^ 6 * Δ := mul_le_mul_of_nonneg_right hN1 hΔ.le
  have hnΔ : N * Δ ≤ 1 / 2 := by linarith
  have hN2Δ : N ^ 2 * Δ ≤ N ^ 6 * Δ := mul_le_mul_of_nonneg_right hN2 hΔ.le
  have hN5Δ : N ^ 5 * Δ ≤ N ^ 6 * Δ := mul_le_mul_of_nonneg_right hN5 hΔ.le
  have hmΔ' : (m : ℝ) * Δ ≤ N ^ 2 / 2 * Δ := mul_le_mul_of_nonneg_right hmn hΔ.le
  have hmΔ : (m : ℝ) * Δ ≤ 1 / 2 := by linarith
  have h2mΔ : 2 * (m : ℝ) * Δ ≤ 1 / 6 := by linarith
  have hΔ1 : Δ ≤ 1 / 6 := by
    have := mul_le_mul_of_nonneg_right hN6 hΔ.le
    linarith
  have hm3 : (m : ℝ) ^ 3 ≤ N ^ 6 / 8 := by
    calc (m : ℝ) ^ 3 ≤ (N ^ 2 / 2) ^ 3 := pow_le_pow_left₀ hm0 hmn 3
      _ = N ^ 6 / 8 := by ring
  have hm3Δ : (m : ℝ) ^ 3 * Δ ≤ 1 / 48 := by
    have := mul_le_mul_of_nonneg_right hm3 hΔ.le
    linarith
  -- the two terms of the forest expansion
  have hgamma := gamma_eq H hP W
  have h1 := term1_ge hcyc U hΔ hdeg hmΔ
  have h2 := term2_ge hodd U hΔ.le hdeg
  -- the cycle sum
  set G : ℕ → ℝ := fun s ↦ ((cycleSets H s).card : ℝ) *
    ((1 + Δ) ^ m - if s = g then 1 else 0) * Qs U s with hG
  have hG0 : ∀ s < g, G s = 0 := by
    intro s hs
    simp only [hG, cycleSets_eq_empty_of_lt_girth hs, Finset.card_empty, Nat.cast_zero, zero_mul]
  have hsplit := sum_range_split (f := G) hgn hG0
  have hpow := one_add_pow_le hΔ.le hmΔ
  set c : ℝ := ((cycleSets H g).card : ℝ) with hc
  have hcg1 : (1 : ℝ) ≤ c := by
    rw [hc]; exact_mod_cast Finset.card_pos.mpr (cycleSets_girth_nonempty hcyc)
  have hcg3 : c ≤ N ^ 3 := by
    have := card_cycleSets_le H hodd (le_refl g)
    rw [Nat.sub_self, zero_add] at this
    rw [hc, hN]; exact_mod_cast this
  have hQg0 : 0 ≤ Qs U g := Qs_nonneg U g
  have hGg : G g ≤ c * (2 * m * Δ) * Qs U g := by
    have hw : (1 + Δ) ^ m - (if g = g then (1 : ℝ) else 0) ≤ 2 * m * Δ := by
      rw [if_pos rfl]; linarith
    calc G g = c * ((1 + Δ) ^ m - if g = g then 1 else 0) * Qs U g := rfl
      _ ≤ c * (2 * m * Δ) * Qs U g := by gcongr
  have hcs : ∀ j, ((cycleSets H (g + 1 + j)).card : ℝ) ≤ N ^ (j + 4) := by
    intro j
    have := card_cycleSets_le H hodd (show g ≤ g + 1 + j by omega)
    rw [show g + 1 + j - g + 3 = j + 4 by omega] at this
    rw [hN]; exact_mod_cast this
  have hw : ∀ j, ((1 + Δ) ^ m - if g + 1 + j = g then 1 else 0) ≤ 2 := by
    intro j
    rw [if_neg (by omega), sub_zero]
    linarith
  have hw0 : ∀ j, 0 ≤ (1 + Δ) ^ m - if g + 1 + j = g then (1 : ℝ) else 0 := by
    intro j
    rw [if_neg (by omega), sub_zero]; positivity
  have hX' : 0 ≤ (1 - (m : ℝ) ^ 3 * Δ) * X := mul_nonneg (by linarith) hX0
  rw [← sub_nonneg, hgamma]
  rcases (show g = 3 ∨ 5 ≤ g from by obtain ⟨r, hr⟩ := hodd; omega) with h3 | h5
  · -- girth three: Lemma 4.6
    have htri : ∀ j, j < n - g → G (g + 1 + j) ≤ 2 * N ^ 4 * (N * Δ) ^ (j + 1) * Qs U g := by
      intro j hj
      have hQ := Qs_le_triangle U hΔ.le hdeg (j + 1)
      rw [show j + 1 + 3 = g + 1 + j by omega, ← h3] at hQ
      have hj' : ((j + 1 : ℕ) : ℝ) + 1 ≤ N := by
        have : ((j + 1 + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : j + 1 + 1 ≤ n)
        push_cast at this ⊢; linarith
      have hQ' : Qs U (g + 1 + j) ≤ N * Δ ^ (j + 1) * Qs U g := by
        have h0 := mul_le_mul_of_nonneg_right hj' (mul_nonneg (pow_nonneg hΔ.le (j + 1)) hQg0)
        linarith
      calc G (g + 1 + j) = ((cycleSets H (g + 1 + j)).card : ℝ) *
            ((1 + Δ) ^ m - if g + 1 + j = g then 1 else 0) * Qs U (g + 1 + j) := rfl
        _ ≤ N ^ (j + 4) * 2 * (N * Δ ^ (j + 1) * Qs U g) := by
            have hQ0 := Qs_nonneg U (g + 1 + j)
            gcongr
            all_goals first | exact hw0 j | exact hcs j | exact hw j | exact hQ'
        _ = 2 * N ^ 4 * (N * Δ) ^ (j + 1) * Qs U g := by ring
    have hsumj : ∑ j ∈ Finset.range (n - g), G (g + 1 + j) ≤ 4 * N ^ 5 * Δ * Qs U g := by
      have hgeo := geom_le (mul_nonneg hN0 hΔ.le) hnΔ (n - g)
      calc _ ≤ ∑ j ∈ Finset.range (n - g), 2 * N ^ 4 * (N * Δ) ^ (j + 1) * Qs U g :=
            Finset.sum_le_sum fun j hj ↦ htri j (Finset.mem_range.mp hj)
        _ = 2 * N ^ 4 * Qs U g * ∑ j ∈ Finset.range (n - g), (N * Δ) ^ (j + 1) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ by ring
        _ ≤ 2 * N ^ 4 * Qs U g * (2 * (N * Δ)) :=
            mul_le_mul_of_nonneg_left hgeo (mul_nonneg (by positivity) hQg0)
        _ = 4 * N ^ 5 * Δ * Qs U g := by ring
    have hcoef : 0 ≤ c * (1 - 2 * m * Δ) - 4 * N ^ 5 * Δ := by
      have h1' : 0 ≤ (c - 1) * (1 - 2 * m * Δ) := mul_nonneg (by linarith) (by linarith)
      have h2' : 4 * N ^ 5 * Δ ≤ 2 / 3 := by linarith
      linarith
    have hkey := mul_nonneg hcoef hQg0
    have hT2 : 0 ≤ c * Qs U g - ∑ s ∈ Finset.range (n + 1), G s := by
      rw [hsplit]
      have : (c * (1 - 2 * m * Δ) - 4 * N ^ 5 * Δ) * Qs U g =
          c * Qs U g - c * (2 * m * Δ) * Qs U g - 4 * N ^ 5 * Δ * Qs U g := by ring
      linarith
    linarith
  · -- girth at least five: the cycle comparison
    obtain ⟨hcomp, hSg⟩ := hspec h5
    obtain ⟨Sg, hSgdef⟩ : ∃ x, x = Ss U g := ⟨_, rfl⟩
    rw [← hSgdef] at hcomp hSg
    have hQS : ∀ s, 2 ≤ s → s ≤ n → |Qs U s - Ss U s| ≤ N ^ 2 * Δ ^ (s - 3) * X := by
      intro s hs2 hsn
      obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
      have h := abs_Qs_sub_Ss_le U hΔ hdeg k
      have hch : 2 * (((k + 1).choose 2 : ℕ) : ℝ) ≤ N ^ 2 :=
        two_choose_two_le k n (by omega)
      have hΔ2 : 0 < Δ ^ 2 := by positivity
      by_cases hk : 1 ≤ k
      · have hpow' : Δ ^ (k + 1) = Δ ^ 2 * Δ ^ (k + 2 - 3) := by
          rw [← pow_add]; congr 1; omega
        rw [hpow'] at h
        have hp := mul_nonneg (mul_nonneg (pow_nonneg hΔ.le (k + 2 - 3)) hX0) hΔ2.le
        have h' : 2 * (((k + 1).choose 2 : ℕ) : ℝ) * (Δ ^ 2 * Δ ^ (k + 2 - 3)) * X ≤
            Δ ^ 2 * (N ^ 2 * Δ ^ (k + 2 - 3) * X) := by
          have := mul_le_mul_of_nonneg_right hch hp
          linarith
        exact le_of_mul_le_mul_left (h.trans h') hΔ2
      · have hk0 : k = 0 := by omega
        subst hk0
        simp only [zero_add, Nat.choose_one_right] at h
        norm_num at h
        have : |Qs U 2 - Ss U 2| = 0 :=
          le_antisymm (le_of_mul_le_mul_left (by linarith) hΔ2) (abs_nonneg _)
        rw [this]; positivity
    -- the terms with `s > g`
    have hterm : ∀ j, j < n - g → G (g + 1 + j) ≤
        N ^ 5 * (N * Δ) ^ (j + 1) * (Sg / 3 + 2 * Δ ^ (g - 3) * X) := by
      intro j hj
      have hs : g < g + 1 + j := by omega
      have hsn : g + 1 + j ≤ n := by omega
      have hS := hcomp (g + 1 + j) hs hsn
      have hQ := hQS (g + 1 + j) (by omega) hsn
      rw [show g + 1 + j - g = j + 1 by omega] at hS
      have hp : Δ ^ (g + 1 + j - 3) = Δ ^ (j + 1) * Δ ^ (g - 3) := by
        rw [← pow_add]; congr 1; omega
      rw [hp] at hQ
      have hQle : Qs U (g + 1 + j) ≤ N ^ 2 / 6 * Δ ^ (j + 1) * Sg +
          N ^ 2 * (Δ ^ (j + 1) * Δ ^ (g - 3)) * X := by
        have := le_abs_self (Qs U (g + 1 + j) - Ss U (g + 1 + j))
        linarith
      have hQ0 := Qs_nonneg U (g + 1 + j)
      calc G (g + 1 + j) = ((cycleSets H (g + 1 + j)).card : ℝ) *
            ((1 + Δ) ^ m - if g + 1 + j = g then 1 else 0) * Qs U (g + 1 + j) := rfl
        _ ≤ N ^ (j + 4) * 2 * (N ^ 2 / 6 * Δ ^ (j + 1) * Sg +
              N ^ 2 * (Δ ^ (j + 1) * Δ ^ (g - 3)) * X) := by
            gcongr
            all_goals first | exact hw0 j | exact hcs j | exact hw j | exact hQle
        _ = N ^ 5 * (N * Δ) ^ (j + 1) * (Sg / 3 + 2 * Δ ^ (g - 3) * X) := by ring
    have hB0 : 0 ≤ Sg / 3 + 2 * Δ ^ (g - 3) * X := by
      have h1 := pow_nonneg hΔ.le (g - 3)
      have h2 := mul_nonneg h1 hX0
      linarith
    have hsumj : ∑ j ∈ Finset.range (n - g), G (g + 1 + j) ≤
        2 * N ^ 6 * Δ * (Sg / 3 + 2 * Δ ^ (g - 3) * X) := by
      have hgeo := geom_le (mul_nonneg hN0 hΔ.le) hnΔ (n - g)
      calc _ ≤ ∑ j ∈ Finset.range (n - g), N ^ 5 * (N * Δ) ^ (j + 1) *
              (Sg / 3 + 2 * Δ ^ (g - 3) * X) :=
            Finset.sum_le_sum fun j hj ↦ hterm j (Finset.mem_range.mp hj)
        _ = N ^ 5 * (Sg / 3 + 2 * Δ ^ (g - 3) * X) *
              ∑ j ∈ Finset.range (n - g), (N * Δ) ^ (j + 1) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ by ring
        _ ≤ N ^ 5 * (Sg / 3 + 2 * Δ ^ (g - 3) * X) * (2 * (N * Δ)) :=
            mul_le_mul_of_nonneg_left hgeo (mul_nonneg (pow_nonneg hN0 5) hB0)
        _ = 2 * N ^ 6 * Δ * (Sg / 3 + 2 * Δ ^ (g - 3) * X) := by ring
    -- `Q_g ≥ S_g - n² Δ^{g-3} X`
    have hQg := hQS g (by omega) hgn
    have hQgS : Sg - N ^ 2 * Δ ^ (g - 3) * X ≤ Qs U g := by
      have := neg_abs_le (Qs U g - Ss U g); linarith
    have hΔg : Δ ^ (g - 3) ≤ Δ ^ 2 :=
      pow_le_pow_of_le_one hΔ.le (by linarith) (by omega)
    have hΔg0 : 0 ≤ Δ ^ (g - 3) := pow_nonneg hΔ.le _
    -- coefficients
    have hc0 : 0 ≤ 1 - 2 * (m : ℝ) * Δ := by linarith
    have hcoefS : 0 ≤ c * (1 - 2 * m * Δ) - 2 / 3 * N ^ 6 * Δ := by
      have h1' : 0 ≤ (c - 1) * (1 - 2 * m * Δ) := mul_nonneg (by linarith) hc0
      linarith
    have hcN : c * N ^ 2 ≤ N ^ 5 := by
      calc c * N ^ 2 ≤ N ^ 3 * N ^ 2 := mul_le_mul_of_nonneg_right hcg3 (sq_nonneg N)
        _ = N ^ 5 := by ring
    have hX1 : c * N ^ 2 * Δ ^ (g - 3) ≤ 1 / 36 := by
      have e1 : c * N ^ 2 * Δ ^ (g - 3) ≤ N ^ 5 * Δ ^ 2 :=
        (mul_le_mul_of_nonneg_right hcN hΔg0).trans
          (mul_le_mul_of_nonneg_left hΔg (by positivity))
      have e2 : N ^ 5 * Δ ^ 2 ≤ N ^ 6 * Δ * Δ := by
        have := mul_le_mul_of_nonneg_right hN5Δ hΔ.le
        linarith only [this]
      have e3 : N ^ 6 * Δ * Δ ≤ 1 / 6 * (1 / 6) :=
        mul_le_mul hΔn hΔ1 hΔ.le (by norm_num)
      linarith only [e1, e2, e3]
    have hX2 : 4 * N ^ 6 * Δ * Δ ^ (g - 3) ≤ 1 / 54 := by
      have e1 : 4 * N ^ 6 * Δ * Δ ^ (g - 3) ≤ 4 * (N ^ 6 * Δ) * Δ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hΔg (show (0 : ℝ) ≤ 4 * (N ^ 6 * Δ) by positivity)
        linarith only [this]
      have e2 : Δ ^ 2 ≤ 1 / 36 := by
        calc Δ ^ 2 = Δ * Δ := sq Δ
          _ ≤ (1 / 6) * (1 / 6) := mul_le_mul hΔ1 hΔ1 hΔ.le (by norm_num)
          _ = 1 / 36 := by norm_num
      have e3 : 4 * (N ^ 6 * Δ) * Δ ^ 2 ≤ 4 * (1 / 6) * (1 / 36) := by
        have := mul_le_mul hΔn e2 (sq_nonneg Δ) (by norm_num)
        linarith only [this]
      linarith only [e1, e3]
    have hcoefX : 0 ≤ 1 - (m : ℝ) ^ 3 * Δ - c * N ^ 2 * Δ ^ (g - 3) -
        4 * N ^ 6 * Δ * Δ ^ (g - 3) := by linarith only [hm3Δ, hX1, hX2]
    -- assemble
    have hA := mul_nonneg hcoefS hSg
    have hB := mul_nonneg hcoefX hX0
    have hQc : c * (1 - 2 * m * Δ) * (Sg - N ^ 2 * Δ ^ (g - 3) * X) ≤
        c * (1 - 2 * m * Δ) * Qs U g :=
      mul_le_mul_of_nonneg_left hQgS (mul_nonneg (by linarith) hc0)
    have hcx : c * (1 - 2 * m * Δ) * (N ^ 2 * Δ ^ (g - 3) * X) ≤ c * (N ^ 2 * Δ ^ (g - 3) * X) := by
      have hpos : 0 ≤ c * (2 * m * Δ) * (N ^ 2 * Δ ^ (g - 3) * X) := by
        have := mul_nonneg (mul_nonneg (sq_nonneg N) hΔg0) hX0
        have h2 : 0 ≤ c * (2 * m * Δ) := mul_nonneg (by linarith) (by positivity)
        exact mul_nonneg h2 this
      linarith only [hpos]
    have hT2 : 0 ≤ (1 - (m : ℝ) ^ 3 * Δ) * X + (c * Qs U g - ∑ s ∈ Finset.range (n + 1), G s) := by
      rw [hsplit]
      linarith only [hA, hB, hQc, hcx, hGg, hsumj]
    linarith only [hT2, h1, h2]

end Taeyoung.Paper.Eventual
