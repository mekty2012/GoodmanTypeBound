import Taeyoung.Paper.Eventual.Expansion
import Taeyoung.Paper.Eventual.Closed

/-!
# Even girth (`paper.pdf`, Proposition 4.17)

For the constant graphon `W ≡ 1 - q` the forest expansion collapses to
`t(H,W) - Ψ_H(q) = ∑_{B(F) ≠ ∅} (-1)^{|F|} q^{|F|} (1-q)^{|B(F)|}`, `Ψ_H(q) = Φ_H(1-q)`.
Forests with a closed edge have at least `g - 1` edges, and those with exactly
`g - 1` are the shortest cycles with their largest edge deleted.  If `g` is
even these leading terms are negative, so `t(H,W) < Ψ_H(q)` for small `q > 0`:
`T_k` is not optimal for any `k > m + 2^m` (`not_turanOptimal_of_even_girth`).
The paper instead reads off the leading term (4.38) from the rank
expansion via Lemma 4.16, and states "sufficiently large `k`".
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Paper.Eventual

open Taeyoung Taeyoung.Methods.PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Constant graphons -/

/-- The constant graphon `W ≡ c` on a one-point space. -/
noncomputable def constGraphon (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    Graphon Unit (Measure.dirac ()) where
  toFun _ _ := c
  measurable := measurable_const
  nonneg _ _ := h0
  le_one _ _ := h1
  symm _ _ := rfl

lemma edgeValue_of_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (K : Graphon Ω μ)
    {c : ℝ} (hK : ∀ x y, K x y = c) (x : V → Ω) (e : Sym2 V) : edgeValue K x e = c := by
  induction e using Sym2.inductionOn with
  | _ u v => rw [edgeValue_mk, hK]

lemma homDensity_constGraphon (H : SimpleGraph V) [DecidableRel H.Adj] (c : ℝ) (h0 : 0 ≤ c)
    (h1 : c ≤ 1) : homDensity H (constGraphon c h0 h1) = c ^ H.edgeFinset.card := by
  unfold homDensity graphWeight
  simp_rw [edgeValue_of_const (constGraphon c h0 h1) (fun _ _ ↦ rfl)]
  simp

lemma edgeDensity_constGraphon (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    edgeDensity (constGraphon c h0 h1) = c := by
  rw [edgeDensity, cliqueDensity, homDensity_constGraphon, Paper.edgeFinset_top_two_card,
    pow_one]

/-! ### The expansion at a constant graphon -/

lemma wInt_of_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (κ : Sym2 V → Graphon Ω μ) (c : Sym2 V → ℝ) (hκ : ∀ e x y, κ e x y = c e)
    (S : Finset (Sym2 V)) : wInt κ S (fun _ ↦ BddFun.one) = ∏ e ∈ S, c e := by
  have h : ∀ (x : V → Ω) e, edgeValue (κ e) x e = c e := fun x e ↦
    edgeValue_of_const (κ e) (hκ e) x e
  unfold wInt edgeProd vertexProd
  simp_rw [h]
  simp [BddFun.one]

/-- **The constant-graphon identity.** -/
theorem homDensity_const_sub (H : SimpleGraph V) [DecidableRel H.Adj] {P : ℝ[X]}
    (hP : IsChromaticPolynomial H P) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    homDensity H (constGraphon (1 - q) (by linarith) (by linarith)) -
        chromaticTarget (V := V) P (1 - q) =
      ∑ F ∈ (forests H.edgeFinset).filter (fun F ↦ closedEdges H.edgeFinset F ≠ ∅),
        (-1) ^ F.card * (q ^ F.card * (1 - q) ^ (closedEdges H.edgeFinset F).card) := by
  classical
  set W := constGraphon (1 - q) (by linarith) (by linarith)
  have hp : edgeDensity W = 1 - q := edgeDensity_constGraphon _ _ _
  have := gamma_eq H hP W
  rw [hp] at this
  rw [this]
  have hWc : ∀ x y, W.compl x y = q := fun x y ↦ by
    show 1 - (1 - q) = q
    ring
  have hmean : meanDeg W.compl = q := by
    unfold meanDeg degree; simp only [hWc]; simp
  have hfirst : ∑ F ∈ openForests H.edgeFinset,
      (-1) ^ F.card * (forestDens W.compl F - meanDeg W.compl ^ F.card) = 0 := by
    refine Finset.sum_eq_zero fun F _ ↦ ?_
    rw [forestDens, wInt_of_const _ (fun _ ↦ q) (fun _ ↦ hWc), hmean]
    simp
  rw [hfirst, zero_add]
  refine Finset.sum_congr rfl fun F hF ↦ ?_
  congr 1
  unfold intervalInt
  rw [wInt_of_const _ (fun e ↦ if e ∈ closedEdges H.edgeFinset F then 1 - q else q)]
  · rw [Finset.prod_union (disjoint_closedEdges _ F)]
    congr 1
    · rw [Finset.prod_congr rfl fun e he ↦ if_neg (Finset.disjoint_left.mp
        (disjoint_closedEdges _ F) he)]
      simp
    · rw [Finset.prod_congr rfl fun e he ↦ if_pos he]
      simp
  · intro e x y
    by_cases he : e ∈ closedEdges H.edgeFinset F
    · rw [closedKernel_of_mem _ he, if_pos he, compl_apply, hWc]
    · rw [closedKernel_of_notMem _ he, if_neg he, hWc]

/-! ### Even girth -/

lemma card_forests_le (E : Finset (Sym2 V)) : (forests E).card ≤ 2 ^ E.card := by
  classical
  calc (forests E).card ≤ E.powerset.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ E.card := Finset.card_powerset E

/-- There is a shortest cycle, hence a leading forest. -/
lemma leadingForests_nonempty (H : SimpleGraph V) [DecidableRel H.Adj] (hcyc : ¬ H.IsAcyclic) :
    (leadingForests H).Nonempty := by
  classical
  obtain ⟨w, c, hc, hlen⟩ := H.exists_girth_eq_length.mpr hcyc
  have hC : c.edges.toFinset ∈ cycleSets H H.girth := by
    refine mem_cycleSets.mpr ⟨fun e he ↦ SimpleGraph.mem_edgeFinset.mpr
      (c.edges_subset_edgeSet (List.mem_toFinset.mp he)), ?_, w, c, hc, rfl⟩
    rw [← length_eq_card_of_cycle hc, hlen]
  have h1 : 0 < (cycleSets H H.girth).card := Finset.card_pos.mpr ⟨_, hC⟩
  exact Finset.card_pos.mp (lt_of_lt_of_le h1 card_cycleSets_le_card_leading)

/-- **Proposition 4.17.**  If the girth of `H` is even, the
constant graphon of density `1 - 1/k` beats `T_k` for every `k > m + 2^m`. -/
theorem not_turanOptimal_of_even_girth (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcyc : ¬ H.IsAcyclic) (heven : Even H.girth) (k : ℕ) [NeZero k]
    (hk : H.edgeFinset.card + 2 ^ H.edgeFinset.card < k) : ¬ TuranOptimal H k := by
  classical
  intro hopt
  obtain ⟨P, hP⟩ := Paper.exists_isChromaticPolynomial H
  set m := H.edgeFinset.card with hm
  set g := H.girth with hg
  have hg3 : 3 ≤ g := H.three_le_girth hcyc
  set q : ℝ := 1 / (k : ℝ) with hqdef
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hq0 : 0 < q := by positivity
  have hkq : (k : ℝ) * q = 1 := by rw [hqdef]; field_simp
  have hk' : ((m : ℝ) + 2 ^ m) < k := by exact_mod_cast hk
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one hkpos]
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  -- `T_k` is no better than the constant graphon
  set W := constGraphon (1 - q) (by linarith) (by linarith)
  have hW := hopt W (by rw [edgeDensity_constGraphon])
  rw [Paper.homDensity_turan_eq_chromaticTarget hP k] at hW
  have hdiff := homDensity_const_sub H hP hq0.le hq1
  -- split the closed forests into the leading ones and the rest
  set T := (forests H.edgeFinset).filter (fun F ↦ closedEdges H.edgeFinset F ≠ ∅)
  set L := leadingForests H
  have hLT : L ⊆ T := by
    intro F hF
    obtain ⟨h1, h2, -⟩ := mem_leadingForests.mp hF
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
  have hterm : ∀ F, (-1) ^ F.card * (q ^ F.card * (1 - q) ^ (closedEdges H.edgeFinset F).card) ≤
      q ^ F.card := by
    intro F
    have h1 : (1 - q) ^ (closedEdges H.edgeFinset F).card ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h2 : 0 ≤ (1 - q) ^ (closedEdges H.edgeFinset F).card := pow_nonneg (by linarith) _
    rcases neg_one_pow_eq_or ℝ F.card with h | h <;> rw [h]
    · nlinarith [pow_pos hq0 F.card]
    · nlinarith [pow_pos hq0 F.card]
  have hlead : ∀ F ∈ L, (-1) ^ F.card * (q ^ F.card * (1 - q) ^ (closedEdges H.edgeFinset F).card)
      ≤ -(q ^ (g - 1) * (1 - q) ^ m) := by
    intro F hF
    obtain ⟨hFf, -, hcard⟩ := mem_leadingForests.mp hF
    have hFcard : F.card = g - 1 := by omega
    have hodd : Odd F.card := by
      rw [hFcard]; obtain ⟨r, hr⟩ := heven; exact ⟨r - 1, by omega⟩
    rw [hodd.neg_one_pow, hFcard]
    have hBm : (closedEdges H.edgeFinset F).card ≤ m :=
      Finset.card_le_card (closedEdges_subset _ _)
    have : (1 - q) ^ m ≤ (1 - q) ^ (closedEdges H.edgeFinset F).card :=
      pow_le_pow_of_le_one (by linarith) (by linarith) hBm
    have hq' : 0 < q ^ (g - 1) := pow_pos hq0 _
    nlinarith
  have hrest : ∀ F ∈ T \ L, (-1) ^ F.card * (q ^ F.card * (1 - q) ^ (closedEdges H.edgeFinset F).card)
      ≤ q ^ g := by
    intro F hF
    obtain ⟨hFT, hFL⟩ := Finset.mem_sdiff.mp hF
    obtain ⟨hFf, hB⟩ := Finset.mem_filter.mp hFT
    have hFE := (mem_forests.mp hFf).1
    have h1 := girth_le_card_add_one hFE hB
    have h2 : F.card + 1 ≠ g := by
      intro h
      exact hFL (mem_leadingForests.mpr ⟨hFf, hB, h⟩)
    exact (hterm F).trans (pow_le_pow_of_le_one hq0.le hq1 (by omega))
  have hsum := Finset.sum_sdiff hLT (f := fun F ↦
    (-1) ^ F.card * (q ^ F.card * (1 - q) ^ (closedEdges H.edgeFinset F).card))
  have hLsum : ∑ F ∈ L, (-1) ^ F.card * (q ^ F.card * (1 - q) ^ (closedEdges H.edgeFinset F).card)
      ≤ -(q ^ (g - 1) * (1 - q) ^ m) := by
    obtain ⟨F0, hF0⟩ := leadingForests_nonempty H hcyc
    rw [← Finset.add_sum_erase L _ hF0]
    have h1 := hlead F0 hF0
    have h2 : ∑ F ∈ L.erase F0, (-1) ^ F.card *
        (q ^ F.card * (1 - q) ^ (closedEdges H.edgeFinset F).card) ≤ 0 :=
      Finset.sum_nonpos fun F hF ↦ (hlead F (Finset.mem_of_mem_erase hF)).trans
        (neg_nonpos.mpr (mul_nonneg (pow_nonneg hq0.le _) (pow_nonneg (by linarith) _)))
    linarith
  have hRsum : ∑ F ∈ T \ L, (-1) ^ F.card * (q ^ F.card * (1 - q) ^ (closedEdges H.edgeFinset F).card)
      ≤ 2 ^ m * q ^ g := by
    calc _ ≤ ∑ _F ∈ T \ L, q ^ g := Finset.sum_le_sum hrest
      _ = (T \ L).card * q ^ g := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ m * q ^ g := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hq0.le _)
          have h1 : (T \ L).card ≤ 2 ^ m :=
            (Finset.card_le_card (Finset.sdiff_subset.trans (Finset.filter_subset _ _))).trans
              (card_forests_le _)
          exact_mod_cast h1
  -- Bernoulli: `(1-q)^m ≥ 1 - mq`
  have hbern : 1 - m * q ≤ (1 - q) ^ m := by
    have := one_add_mul_le_pow (a := -q) (by linarith) m
    simpa [sub_eq_add_neg] using this
  have hg1 : q ^ g = q ^ (g - 1) * q := by
    rw [← pow_succ]; congr 1; omega
  have hneg : homDensity H W - chromaticTarget (V := V) P (1 - q) < 0 := by
    rw [hdiff, ← hsum]
    have hq' : 0 < q ^ (g - 1) := pow_pos hq0 _
    have hsmall : (m + 2 ^ m) * q < 1 := by
      calc (m + 2 ^ m) * q < k * q := by
            exact mul_lt_mul_of_pos_right hk' hq0
        _ = 1 := hkq
    nlinarith
  have hW' : chromaticTarget (V := V) P (1 - 1 / (k : ℝ)) ≤ homDensity H W := hW
  rw [← hqdef] at hW'
  linarith

end Taeyoung.Paper.Eventual
