import Taeyoung.Paper.Profile.Reference
import Taeyoung.Paper.Turan

/-!
# The clique-tree criterion (`paper.pdf`, Lemma 1.2, Proposition 2.1)

**Lemma 1.2.** Let `H` be a connected chordal graph of clique number
`k ≥ 3`, with maximal cliques `C_1, …, C_m` and a clique tree `T`; put `r_i = |C_i|`,
`s_e = |C_i ∩ C_j|` for `e = ij ∈ E(T)`, and
`b_j = #{i : r_i ≥ j} - #{e ∈ E(T) : s_e ≥ j}` (1.5).  If `b_1 ≤ b_2 ≤ ⋯ ≤ b_k`,
then `H` satisfies the Goodman-type lower bound (`satisfiesLowerBound_of_profile`,
`chordal_satisfiesLowerBound_of_profile`).  In Lean the tree is a rooted
`MaximalCliqueTreeDecomp`, `s_i = |S_i|` is the size of the separator of bag `i`
with its parent (`S_root = ∅`), and connectedness is not assumed.

The pieces, all for an arbitrary maximal-clique tree `D`:

* `P_H = ∏_i ∏_{s_i ≤ j < r_i} (X - j)` and `χ(H) = k` (`Paper/Profile/Extension.lean`);
* **Proposition 2.1**: `∏_i t(K_{r_i},W) ≤ t(H,W) ∏_i t(K_{s_i},W)`, which is
  `t(H,W) ∏_{j<k} t_j^{b_{j+1}-b_j} ≥ t_k^{b_k}` (`gluing_inequality`);
* the Moon–Moser step (Lemma 2.2, Lemma 2.3) `t_{j+1} ≥ c_{j+1}(p) t_j` for
  `j < k`, with `c_j(p) = 1 - (j-1)(1-p)` as in (2.2).
-/

open MeasureTheory Finset Polynomial
open scoped ENNReal

namespace Taeyoung.Paper.Profile

open Taeyoung Taeyoung.Methods.PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
  {m : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : MaximalCliqueTreeDecomp H m) (k : ℕ) (hk : ∀ i, (D.bag i).card ≤ k)
variable {δ : ℝ}

/-! ### The clique-tree identity on the original coordinates -/

/-- A pair of original vertices. -/
def IsOrigPair (e : Sym2 (ExtV D k)) : Prop := ∀ v ∈ e, Sum.isLeft v = true

lemma isOrigPair_mk {u v : ExtV D k} : IsOrigPair D k s(u, v) ↔ u.isLeft ∧ v.isLeft := by
  simp [IsOrigPair, Sym2.mem_iff, or_imp, forall_and]

include hk in
/-- `κ_H ∏_i κ_{S_i} = ∏_i κ_{C_i}`, read on the original coordinates. -/
lemma graphWeight_mul_prod_liftSep (W : Graphon Ω μ) (x : ExtV D k → Ω) :
    graphWeight H W (fun v ↦ x (Sum.inl v)) *
        ∏ i, PureCliqueTreeDecomp.cliqueWeightOn (liftSep D k i) W x =
      ∏ i, PureCliqueTreeDecomp.cliqueWeightOn (liftBag D k i) W x := by
  classical
  let f : Sym2 (ExtV D k) → ℝ := fun e ↦ if IsOrigPair D k e then edgeValue W x e else 1
  have hpure := (extDecomp D k hk).prod_pairsIn_bags f
  -- pairs inside a set of original vertices
  have hT1 : ∀ A : Finset (ExtV D k), (∀ v ∈ A, Sum.isLeft v = true) →
      ∏ e ∈ pairsIn A, f e = PureCliqueTreeDecomp.cliqueWeightOn A W x := by
    intro A hA
    unfold PureCliqueTreeDecomp.cliqueWeightOn
    refine Finset.prod_congr rfl fun e he ↦ ?_
    have : IsOrigPair D k e := by
      induction e using Sym2.inductionOn with
      | _ u v =>
        rw [mk_mem_pairsIn] at he
        exact (isOrigPair_mk D k).mpr ⟨hA u he.2.1, hA v he.2.2⟩
    simp [f, this]
  have hT2 : ∀ i, ∏ e ∈ pairsIn (extBag D k i), f e =
      PureCliqueTreeDecomp.cliqueWeightOn (liftBag D k i) W x := by
    intro i
    unfold PureCliqueTreeDecomp.cliqueWeightOn
    rw [← Finset.prod_filter]
    congr 1
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      rw [Finset.mem_filter, mk_mem_pairsIn, mk_mem_pairsIn, isOrigPair_mk]
      rcases u with a | e₁ <;> rcases v with b | e₂ <;> simp [liftBag]
  have hT3 : ∏ e ∈ (extGraph D k).edgeFinset, f e = graphWeight H W (fun v ↦ x (Sum.inl v)) := by
    rw [← Finset.prod_filter, graphWeight]
    have hset : (extGraph D k).edgeFinset.filter (IsOrigPair D k) =
        H.edgeFinset.map ⟨Sym2.map Sum.inl, Sym2.map.injective Sum.inl_injective⟩ := by
      ext e
      induction e using Sym2.inductionOn with
      | _ u v =>
        rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          isOrigPair_mk, Finset.mem_map]
        constructor
        · rintro ⟨hadj, hu, hv⟩
          rcases u with a | e₁
          · rcases v with b | e₂
            · exact ⟨s(a, b), by
                rw [SimpleGraph.mem_edgeFinset]; exact (extGraph_adj_inl D k).mp hadj, by simp⟩
            · simp at hv
          · simp at hu
        · rintro ⟨e', he', hee⟩
          induction e' using Sym2.inductionOn with
          | _ a b =>
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
            simp only [Function.Embedding.coeFn_mk, Sym2.map_mk, Sym2.eq_iff] at hee
            rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨(extGraph_adj_inl D k).mpr he', by simp, by simp⟩
            · exact ⟨(extGraph_adj_inl D k).mpr he'.symm, by simp, by simp⟩
    rw [hset, Finset.prod_map]
    exact Finset.prod_congr rfl fun e _ ↦ edgeValue_sym2_map W x Sum.inl e
  have hsep : ∀ i, ∏ e ∈ pairsIn ((extDecomp D k hk).separator i), f e =
      PureCliqueTreeDecomp.cliqueWeightOn (liftSep D k i) W x := by
    intro i
    rw [extDecomp_separator_eq]
    apply hT1
    intro v hv
    rcases v with a | e
    · rfl
    · simp [liftSep] at hv
  simp only [extDecomp_bag] at hpure
  simp_rw [hT2, hT3, hsep] at hpure
  rw [hpure]

/-! ### The main Gibbs step -/

/-- `G` as a real function. -/
noncomputable def refDensity (W : Graphon Ω μ) (x : ExtV D k → Ω) : ℝ :=
  (refENN D k W x).toReal

lemma refDensity_eq (W : Graphon Ω μ) (x : ExtV D k → Ω) :
    refDensity D k W x = graphWeight H W (fun v ↦ x (Sum.inl v)) / homDensity H W *
      ∏ i, PureCliqueTreeDecomp.cliqueWeightOn (extBag D k i) W x /
        (margOn W (extBag D k i) (liftBag D k i) x).toReal := by
  unfold refDensity refENN padTrans
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (homDensity_nonneg H W),
    ENNReal.toReal_ofReal (graphWeight_nonneg H W _), ENNReal.toReal_prod]
  congr 1
  · ring
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, cliqueWeightOnENN,
      ENNReal.toReal_ofReal (cliqueWeightOn_nonneg _ W x)]
    ring

/-- **The main Gibbs step**:
`log t(H) ≥ ∑_i E_Q[φ(C'_i, C_i)] - ∑_i E_Q[φ(C'_i, S_i)]`. -/
theorem log_homDensity_ge (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) :
    ∑ i, ∫ x, (extDecomp D k hk).junctionDensity W x * phi W (extBag D k i) (liftBag D k i) x
        ∂Measure.pi (fun _ : ExtV D k ↦ μ) -
      ∑ i, ∫ x, (extDecomp D k hk).junctionDensity W x *
        phi W (extBag D k i) (liftSep D k i) x ∂Measure.pi (fun _ : ExtV D k ↦ μ) ≤
      Real.log (homDensity H W) := by
  set Q := (extDecomp D k hk).junctionDensity W with hQdef
  set G := refDensity D k W with hGdef
  have htH := homDensity_pos_of_lower_bound H W hδpos hδ
  -- positivity of the pieces
  have hκ := fun (A : Finset (ExtV D k)) x ↦ cliqueWeightOn_pos W hδpos hδ A x
  have hm := fun (B A : Finset (ExtV D k)) x ↦ margOn_toReal_pos W hδpos hδ B A x
  have hQpos : ∀ x, 0 < Q x := fun x ↦
    (extDecomp D k hk).junctionDensity_pos W hδpos hδ x
  have hκH : ∀ x : ExtV D k → Ω, 0 < graphWeight H W (fun v ↦ x (Sum.inl v)) := fun x ↦
    lt_of_lt_of_le (pow_pos hδpos _) (graphWeight_lower_bound H W hδpos.le hδ _)
  -- the junction law in closed form
  have hQ : ∀ x, Q x * ∏ i, (margOn W (extBag D k i) (liftSep D k i) x).toReal =
      ∏ i, PureCliqueTreeDecomp.cliqueWeightOn (extBag D k i) W x := by
    intro x
    have h := congrArg ENNReal.toReal
      ((extDecomp D k hk).partialJunctionENN_mul_prod_bagNewMarginalENN W hδpos hδ x)
    rw [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_prod] at h
    simp only [bagNewMarginalENN_eq_margOn D k hk] at h
    rw [hQdef]
    unfold PureCliqueTreeDecomp.junctionDensity
    rw [h]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [PureCliqueTreeDecomp.bagWeightENN_toReal]
    rfl
  -- the logarithm of the ratio
  have hratio : ∀ x, Real.log (G x / Q x) = -Real.log (homDensity H W) +
      ∑ i, phi W (extBag D k i) (liftBag D k i) x - ∑ i, phi W (extBag D k i) (liftSep D k i) x := by
    intro x
    have hGx : G x = _ := refDensity_eq D k W x
    have hid := graphWeight_mul_prod_liftSep D k hk W x
    have hprodS : 0 < ∏ i, (margOn W (extBag D k i) (liftSep D k i) x).toReal :=
      Finset.prod_pos fun i _ ↦ hm _ _ x
    have hprodC : 0 < ∏ i, (margOn W (extBag D k i) (liftBag D k i) x).toReal :=
      Finset.prod_pos fun i _ ↦ hm _ _ x
    have hprodK : 0 < ∏ i, PureCliqueTreeDecomp.cliqueWeightOn (extBag D k i) W x :=
      Finset.prod_pos fun i _ ↦ hκ _ x
    have hprodKS : 0 < ∏ i, PureCliqueTreeDecomp.cliqueWeightOn (liftSep D k i) W x :=
      Finset.prod_pos fun i _ ↦ hκ _ x
    have hprodKC : 0 < ∏ i, PureCliqueTreeDecomp.cliqueWeightOn (liftBag D k i) W x :=
      Finset.prod_pos fun i _ ↦ hκ _ x
    -- the ratio, cleared of denominators
    have hGQ : G x / Q x = graphWeight H W (fun v ↦ x (Sum.inl v)) / homDensity H W *
        (∏ i, (margOn W (extBag D k i) (liftSep D k i) x).toReal) /
        (∏ i, (margOn W (extBag D k i) (liftBag D k i) x).toReal) := by
      rw [hGx, Finset.prod_div_distrib]
      have hQx : Q x = (∏ i, PureCliqueTreeDecomp.cliqueWeightOn (extBag D k i) W x) /
          ∏ i, (margOn W (extBag D k i) (liftSep D k i) x).toReal := by
        rw [eq_div_iff hprodS.ne', hQ x]
      rw [hQx]
      field_simp
    have hlogH : Real.log (graphWeight H W (fun v ↦ x (Sum.inl v))) =
        ∑ i, Real.log (PureCliqueTreeDecomp.cliqueWeightOn (liftBag D k i) W x) -
          ∑ i, Real.log (PureCliqueTreeDecomp.cliqueWeightOn (liftSep D k i) W x) := by
      rw [← Real.log_prod (fun i _ ↦ (hκ _ x).ne'), ← Real.log_prod (fun i _ ↦ (hκ _ x).ne'),
        ← hid, Real.log_mul (hκH x).ne' hprodKS.ne']
      ring
    rw [hGQ, Real.log_div (mul_pos (div_pos (hκH x) htH) hprodS).ne' hprodC.ne',
      Real.log_mul (div_pos (hκH x) htH).ne' hprodS.ne',
      Real.log_div (hκH x).ne' htH.ne', hlogH,
      Real.log_prod (fun i _ ↦ (hm _ _ x).ne'), Real.log_prod (fun i _ ↦ (hm _ _ x).ne')]
    unfold phi
    simp only [Finset.sum_sub_distrib]
    ring
  -- Gibbs
  have hGm : Measurable G := (measurable_refENN D k W).ennreal_toReal
  have hQm : Measurable Q := (extDecomp D k hk).measurable_junctionDensity W
  obtain ⟨aQ, haQ, hQlo⟩ := (extDecomp D k hk).junctionDensity_exists_lower_bound W hδpos hδ
  obtain ⟨bQ, hbQ, hQhi⟩ := (extDecomp D k hk).junctionDensity_exists_upper_bound W hδpos hδ
  have hGlo : ∃ a > 0, ∀ x, a ≤ G x := by
    refine ⟨δ ^ H.edgeFinset.card * ∏ i : Fin m, δ ^ (pairsIn (extBag D k i)).card,
      mul_pos (pow_pos hδpos _) (Finset.prod_pos fun i _ ↦ pow_pos hδpos _), fun x ↦ ?_⟩
    rw [hGdef, refDensity_eq D k W x]
    apply mul_le_mul _ _ (Finset.prod_nonneg fun i _ ↦ (pow_pos hδpos _).le)
      (div_nonneg (graphWeight_nonneg H W _) htH.le)
    · rw [le_div_iff₀ htH]
      calc δ ^ H.edgeFinset.card * homDensity H W ≤ δ ^ H.edgeFinset.card * 1 :=
            mul_le_mul_of_nonneg_left (homDensity_le_one H W) (pow_pos hδpos _).le
        _ ≤ _ := by rw [mul_one]; exact graphWeight_lower_bound H W hδpos.le hδ _
    · refine Finset.prod_le_prod (fun i _ ↦ (pow_pos hδpos _).le) fun i _ ↦ ?_
      rw [le_div_iff₀ (hm _ _ x)]
      calc δ ^ (pairsIn (extBag D k i)).card * (margOn W (extBag D k i) (liftBag D k i) x).toReal
          ≤ δ ^ (pairsIn (extBag D k i)).card * 1 :=
            mul_le_mul_of_nonneg_left (margOn_toReal_le_one W _ _ x) (pow_pos hδpos _).le
        _ ≤ _ := by rw [mul_one]; exact cliqueWeightOn_lower_bound _ W hδpos.le hδ x
  have hGhi : ∃ b > 0, ∀ x, G x ≤ b := by
    refine ⟨1 / homDensity H W * ∏ i : Fin m, 1 / δ ^ (pairsIn (extBag D k i)).card,
      mul_pos (one_div_pos.mpr htH) (Finset.prod_pos fun i _ ↦ one_div_pos.mpr (pow_pos hδpos _)),
      fun x ↦ ?_⟩
    rw [hGdef, refDensity_eq D k W x]
    apply mul_le_mul _ _ (Finset.prod_nonneg fun i _ ↦
      div_nonneg (cliqueWeightOn_nonneg _ W x) (hm _ _ x).le) (one_div_pos.mpr htH).le
    · exact div_le_div_of_nonneg_right (graphWeight_le_one H W _) htH.le
    · refine Finset.prod_le_prod (fun i _ ↦ div_nonneg (cliqueWeightOn_nonneg _ W x)
        (hm _ _ x).le) fun i _ ↦ ?_
      exact div_le_div₀ zero_le_one (cliqueWeightOn_le_one _ W x) (pow_pos hδpos _)
        (margOn_toReal_lower W hδpos hδ _ _ x)
  have hQint : Integrable Q (Measure.pi fun _ : ExtV D k ↦ μ) :=
    integrable_of_bounded hQm bQ fun x ↦ by rw [abs_of_nonneg (hQpos x).le]; exact hQhi x
  obtain ⟨aG, haG, hGlo'⟩ := hGlo
  obtain ⟨bG, hbG, hGhi'⟩ := hGhi
  have hGint : Integrable G (Measure.pi fun _ : ExtV D k ↦ μ) :=
    integrable_of_bounded hGm bG fun x ↦ by
      rw [abs_of_nonneg (haG.le.trans (hGlo' x))]; exact hGhi' x
  have hQ1 := (extDecomp D k hk).integral_junctionDensity_eq_one W hδpos hδ
  have hG1 : ∫ x, G x ∂Measure.pi (fun _ : ExtV D k ↦ μ) = 1 := by
    rw [hGdef]
    unfold refDensity
    rw [integral_toReal (measurable_refENN D k W).aemeasurable
      (ae_lt_top (measurable_refENN D k W) (by rw [lintegral_refENN D k W hδpos hδ]; simp)),
      lintegral_refENN D k W hδpos hδ]
    rfl
  have hgibbs := integral_mul_log_div_nonpos_of_exists_bounds hQm hGm hQint hGint hQ1 hG1
    ⟨aQ, haQ, hQlo⟩ ⟨aG, haG, hGlo'⟩ ⟨bQ, hbQ, hQhi⟩ ⟨bG, hbG, hGhi'⟩
  simp_rw [hratio] at hgibbs
  -- linearity
  have hphiInt : ∀ (A : Fin m → Finset (ExtV D k)) i, Integrable
      (fun x ↦ Q x * phi W (extBag D k i) (A i) x) (Measure.pi fun _ : ExtV D k ↦ μ) := by
    intro A i
    exact integrable_of_bounded (hQm.mul (measurable_phi W _ _))
      (bQ * (-Real.log (δ ^ (pairsIn (A i)).card) - Real.log (δ ^ (pairsIn (extBag D k i)).card)))
      fun x ↦ by
        rw [abs_mul, abs_of_nonneg (hQpos x).le]
        exact mul_le_mul (hQhi x) (abs_phi_le W hδpos hδ _ _ x) (abs_nonneg _) hbQ.le
  have hexpand : ∀ x, Q x * (-Real.log (homDensity H W) +
      ∑ i, phi W (extBag D k i) (liftBag D k i) x - ∑ i, phi W (extBag D k i) (liftSep D k i) x) =
      -Real.log (homDensity H W) * Q x + (∑ i, Q x * phi W (extBag D k i) (liftBag D k i) x -
        ∑ i, Q x * phi W (extBag D k i) (liftSep D k i) x) := by
    intro x
    rw [mul_sub, mul_add, Finset.mul_sum, Finset.mul_sum]
    ring
  simp_rw [hexpand] at hgibbs
  have hB : Integrable (fun x ↦ ∑ i, Q x * phi W (extBag D k i) (liftBag D k i) x)
      (Measure.pi fun _ : ExtV D k ↦ μ) :=
    integrable_finsetSum _ fun i _ ↦ hphiInt (liftBag D k) i
  have hC : Integrable (fun x ↦ ∑ i, Q x * phi W (extBag D k i) (liftSep D k i) x)
      (Measure.pi fun _ : ExtV D k ↦ μ) :=
    integrable_finsetSum _ fun i _ ↦ hphiInt (liftSep D k) i
  have hBC : Integrable (fun x ↦ ∑ i, Q x * phi W (extBag D k i) (liftBag D k i) x -
      ∑ i, Q x * phi W (extBag D k i) (liftSep D k i) x) (Measure.pi fun _ : ExtV D k ↦ μ) :=
    hB.sub hC
  rw [integral_add (hQint.const_mul _) hBC, integral_sub hB hC, integral_const_mul, hQ1,
    integral_finsetSum _ fun i _ ↦ hphiInt (liftBag D k) i,
    integral_finsetSum _ fun i _ ↦ hphiInt (liftSep D k) i] at hgibbs
  linarith

/-! ### Exchangeability levels -/

lemma integral_nb (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (B : Finset (ExtV D k)) :
    ∫ x, nb W B x ∂Measure.pi (fun _ : ExtV D k ↦ μ) = 1 := by
  unfold nb
  rw [integral_div]
  have := integral_cliqueWeightOn (μ := μ) B W
  simp only [assignmentMeasure] at this
  rw [this]
  exact div_self (cliqueDensity_pos' W hδpos hδ _).ne'

/-- The reference bag: the padded root bag, of size `k`. -/
def refBag : Finset (ExtV D k) := extBag D k D.root

/-- A reference subset of the reference bag of each size `j ≤ k`. -/
noncomputable def refSub (j : ℕ) : Finset (ExtV D k) :=
  if h : j ≤ (refBag D k).card then
    Classical.choose (Finset.exists_subset_card_eq (s := refBag D k) h)
  else refBag D k

lemma refSub_subset (j : ℕ) : refSub D k j ⊆ refBag D k := by
  unfold refSub
  split_ifs with h
  · exact (Classical.choose_spec (Finset.exists_subset_card_eq (s := refBag D k) h)).1
  · exact Finset.Subset.refl _

include hk in
lemma card_refSub {j : ℕ} (hj : j ≤ k) : (refSub D k j).card = j := by
  have hcard : (refBag D k).card = k := card_extBag hk D.root
  have h : j ≤ (refBag D k).card := by rw [hcard]; exact hj
  unfold refSub
  rw [dif_pos h]
  exact (Classical.choose_spec (Finset.exists_subset_card_eq (s := refBag D k) h)).2

/-- `γ_j = E_{ρ_k}[log κ_A - log m(A)]` for any `j`-subset `A` of a `k`-bag. -/
noncomputable def gamma (W : Graphon Ω μ) (j : ℕ) : ℝ :=
  ∫ x, nb W (refBag D k) x * phi W (refBag D k) (refSub D k j) x
    ∂Measure.pi (fun _ : ExtV D k ↦ μ)

include hk in
lemma integral_phi_eq_gamma (W : Graphon Ω μ) (i : Fin m) {A : Finset (ExtV D k)}
    (hA : A ⊆ extBag D k i) (hAk : A.card ≤ k) :
    ∫ x, nb W (extBag D k i) x * phi W (extBag D k i) A x
        ∂Measure.pi (fun _ : ExtV D k ↦ μ) = gamma D k W A.card := by
  unfold gamma
  exact integral_nb_mul_phi_perm W hA (refSub_subset D k _)
    (by rw [card_extBag hk, refBag, card_extBag hk]) (card_refSub D k hk hAk).symm

include hk in
lemma gamma_le (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) {j : ℕ} (hj : j ≤ k) :
    gamma D k W j ≤ Real.log (cliqueDensity j W) - Real.log (cliqueDensity k W) := by
  have h := integral_nb_mul_phi_le W hδpos hδ (refSub_subset D k j)
  rw [card_refSub D k hk hj, refBag, card_extBag hk] at h
  exact h

include hk in
lemma gamma_zero (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) :
    gamma D k W 0 = -Real.log (cliqueDensity k W) := by
  have h0 : refSub D k 0 = ∅ := Finset.card_eq_zero.mp (card_refSub D k hk (Nat.zero_le _))
  have hphi : ∀ x, phi W (refBag D k) (refSub D k 0) x = -Real.log (cliqueDensity k W) := by
    intro x
    rw [h0, phi, margOn_empty]
    simp only [PureCliqueTreeDecomp.cliqueWeightOn]
    have hp : pairsIn (∅ : Finset (ExtV D k)) = ∅ := by
      ext e; induction e using Sym2.inductionOn with | _ u v => simp [mk_mem_pairsIn]
    rw [hp, Finset.prod_empty, Real.log_one, refBag, card_extBag hk,
      ENNReal.toReal_ofReal (cliqueDensity_nonneg _ W)]
    ring
  unfold gamma
  simp_rw [hphi]
  rw [integral_mul_const, integral_nb D k W hδpos hδ, one_mul]

include hk in
lemma gamma_k (W : Graphon Ω μ) : gamma D k W k = 0 := by
  have hk' : refSub D k k = refBag D k :=
    Finset.eq_of_subset_of_card_le (refSub_subset D k k)
      (by rw [card_refSub D k hk le_rfl, refBag, card_extBag hk])
  have hphi : ∀ x, phi W (refBag D k) (refSub D k k) x = 0 := by
    intro x
    rw [hk', phi, margOn_self, cliqueWeightOnENN,
      ENNReal.toReal_ofReal (cliqueWeightOn_nonneg _ W x), sub_self]
  unfold gamma
  simp_rw [hphi, mul_zero, integral_zero]

/-! ### The gluing inequality -/

include hk in
/-- A non-root bag is not contained in its parent, so `s_i < k` whenever `3 ≤ k`. -/
lemma s_lt (hk3 : 3 ≤ k) (i : Fin m) : s D i < k := by
  by_cases hi : i = D.root
  · simp [s, sep, hi]; omega
  · by_contra hle
    push Not at hle
    have hsr := s_le_r D i
    have hrk : r D i ≤ k := hk i
    have hsub := sep_subset_bag D i
    have heq : sep D i = D.bag i :=
      Finset.eq_of_subset_of_card_le hsub (by unfold s r at *; omega)
    have hpar : D.bag i ⊆ D.bag (D.parent i) := by
      intro v hv
      rw [← heq] at hv
      simp only [sep, hi, if_false, Finset.mem_inter] at hv
      exact hv.2
    have hcl : H.IsClique (D.bag (D.parent i) : Set V) := (D.bag_maximal (D.parent i)).1
    have h2 : (D.bag (D.parent i) : Set V) ⊆ D.bag i := (D.bag_maximal i).2 hcl (by exact_mod_cast hpar)
    have hbag : D.bag i = D.bag (D.parent i) :=
      Finset.Subset.antisymm hpar (by exact_mod_cast h2)
    have hip := D.bag_injective hbag
    have hlt := D.parent_lt i hi
    rw [← hip] at hlt
    exact Nat.lt_irrefl _ hlt

include hk in
/-- **Gluing, for a graphon bounded below.** -/
theorem gluing_of_lower_bound (hmono : ProfileMonotone D k) (W : Graphon Ω μ)
    (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) :
    ∏ i, cliqueDensity (r D i) W ≤ homDensity H W * ∏ i, cliqueDensity (s D i) W := by
  have hlog := log_homDensity_ge D k hk W hδpos hδ
  -- each expectation is a level value
  have hphiC : ∀ i, ∫ x, (extDecomp D k hk).junctionDensity W x *
      phi W (extBag D k i) (liftBag D k i) x ∂Measure.pi (fun _ : ExtV D k ↦ μ) =
      gamma D k W (r D i) := by
    intro i
    have hdep : ∀ ⦃x y : ExtV D k → Ω⦄, (∀ v ∈ extBag D k i, x v = y v) →
        phi W (extBag D k i) (liftBag D k i) x = phi W (extBag D k i) (liftBag D k i) y := by
      intro x y hxy
      unfold phi
      rw [cliqueWeightOn_congr_on _ W fun v hv ↦ hxy v (liftBag_subset D k i hv),
        margOn_dependsOn W (liftBag_subset D k i) fun v hv ↦ hxy v (liftBag_subset D k i hv)]
    rw [integral_junction_mul D k hk W hδpos hδ i (measurable_phi W _ _)
      (abs_phi_le W hδpos hδ _ _) hdep,
      integral_phi_eq_gamma D k hk W i (liftBag_subset D k i)
        (by rw [card_liftBag]; exact hk i), card_liftBag]
  have hphiS : ∀ i, ∫ x, (extDecomp D k hk).junctionDensity W x *
      phi W (extBag D k i) (liftSep D k i) x ∂Measure.pi (fun _ : ExtV D k ↦ μ) =
      gamma D k W (s D i) := by
    intro i
    have hdep : ∀ ⦃x y : ExtV D k → Ω⦄, (∀ v ∈ extBag D k i, x v = y v) →
        phi W (extBag D k i) (liftSep D k i) x = phi W (extBag D k i) (liftSep D k i) y := by
      intro x y hxy
      unfold phi
      rw [cliqueWeightOn_congr_on _ W fun v hv ↦ hxy v (liftSep_subset D k i hv),
        margOn_dependsOn W (liftSep_subset D k i) fun v hv ↦ hxy v (liftSep_subset D k i hv)]
    rw [integral_junction_mul D k hk W hδpos hδ i (measurable_phi W _ _)
      (abs_phi_le W hδpos hδ _ _) hdep,
      integral_phi_eq_gamma D k hk W i (liftSep_subset D k i)
        (by rw [card_liftSep]; exact (s_le_r D i).trans (hk i)), card_liftSep]
  simp_rw [hphiC, hphiS] at hlog
  -- the deficits `δ_j = (log t_j - log t_k) - γ_j`
  let lam : ℕ → ℝ := fun j ↦ Real.log (cliqueDensity j W) - Real.log (cliqueDensity k W)
  let dfc : ℕ → ℝ := fun j ↦ if j ≤ k then lam j - gamma D k W j else 0
  have hdfc0 : dfc 0 = 0 := by
    simp only [dfc, Nat.zero_le, if_true, lam, gamma_zero D k hk W hδpos hδ, cliqueDensity_zero,
      Real.log_one]
    ring
  have hdfck : dfc k = 0 := by
    simp only [dfc, le_rfl, if_true, lam, gamma_k D k hk W]
    ring
  have hdfc : ∀ j, 0 ≤ dfc j := by
    intro j
    simp only [dfc]
    split_ifs with hj
    · have := gamma_le D k hk W hδpos hδ hj; simp only [lam]; linarith
    · exact le_rfl
  have hrk : ∀ i, r D i ≤ k := hk
  have hsk : ∀ i, s D i ≤ k := fun i ↦ (s_le_r D i).trans (hk i)
  have hgam : ∀ i, gamma D k W (r D i) - gamma D k W (s D i) =
      (lam (r D i) - lam (s D i)) - (dfc (r D i) - dfc (s D i)) := by
    intro i
    simp only [dfc, if_pos (hrk i), if_pos (hsk i)]
    ring
  have htele := sum_bags_telescope D hrk dfc
  have habel := abel_nonpos k (profileB D) dfc hdfc0 hdfck hdfc hmono
  have hsum : ∑ i, (lam (r D i) - lam (s D i)) ≤ Real.log (homDensity H W) := by
    have : ∑ i, gamma D k W (r D i) - ∑ i, gamma D k W (s D i) =
        ∑ i, (lam (r D i) - lam (s D i)) - ∑ i, (dfc (r D i) - dfc (s D i)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      simp_rw [hgam]
      try rw [Finset.sum_sub_distrib]
    rw [htele] at this
    linarith
  -- exponentiate
  have htpos : ∀ j, 0 < cliqueDensity j W := fun j ↦ cliqueDensity_pos' W hδpos hδ j
  have hlogs : ∑ i, (lam (r D i) - lam (s D i)) =
      Real.log (∏ i, cliqueDensity (r D i) W) - Real.log (∏ i, cliqueDensity (s D i) W) := by
    rw [Real.log_prod (fun i _ ↦ (htpos _).ne'), Real.log_prod (fun i _ ↦ (htpos _).ne'),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [lam]
    ring
  rw [hlogs] at hsum
  have hA : 0 < ∏ i, cliqueDensity (s D i) W := Finset.prod_pos fun i _ ↦ htpos _
  have hB : 0 < ∏ i, cliqueDensity (r D i) W := Finset.prod_pos fun i _ ↦ htpos _
  have htH := homDensity_pos_of_lower_bound H W hδpos hδ
  have : Real.log (∏ i, cliqueDensity (r D i) W) ≤
      Real.log (homDensity H W * ∏ i, cliqueDensity (s D i) W) := by
    rw [Real.log_mul htH.ne' hA.ne']; linarith
  exact (Real.log_le_log_iff hB (mul_pos htH hA)).mp this

/-- Removing a positive lower bound by regularization. -/
lemma le_of_regularize (W : Graphon Ω μ) {L R : Graphon Ω μ → ℝ} {CL CR : ℝ}
    (hL : ∀ ε (h0 : 0 ≤ ε) (h1 : ε ≤ 1), |L (W.regularize ε h0 h1) - L W| ≤ CL * ε)
    (hR : ∀ ε (h0 : 0 ≤ ε) (h1 : ε ≤ 1), |R (W.regularize ε h0 h1) - R W| ≤ CR * ε)
    (hLR : ∀ ε (h0 : 0 < ε) (h1 : ε ≤ 1), L (W.regularize ε h0.le h1) ≤ R (W.regularize ε h0.le h1)) :
    L W ≤ R W := by
  have hCL : 0 ≤ CL := by
    have := hL 1 zero_le_one le_rfl
    nlinarith [abs_nonneg (L (W.regularize 1 zero_le_one le_rfl) - L W)]
  have hCR : 0 ≤ CR := by
    have := hR 1 zero_le_one le_rfl
    nlinarith [abs_nonneg (R (W.regularize 1 zero_le_one le_rfl) - R W)]
  apply le_of_forall_pos_le_add
  intro η hη
  set ε := min 1 (η / (CL + CR + 1)) with hε
  have hC : 0 < CL + CR + 1 := by linarith
  have hε0 : 0 < ε := lt_min one_pos (div_pos hη hC)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεη : (CL + CR) * ε ≤ η := by
    have : ε ≤ η / (CL + CR + 1) := min_le_right _ _
    calc (CL + CR) * ε ≤ (CL + CR + 1) * ε := by nlinarith
      _ ≤ (CL + CR + 1) * (η / (CL + CR + 1)) := mul_le_mul_of_nonneg_left this hC.le
      _ = η := by field_simp
  have h1 := (abs_le.mp (hL ε hε0.le hε1)).1
  have h2 := (abs_le.mp (hR ε hε0.le hε1)).2
  have h3 := hLR ε hε0 hε1
  nlinarith

lemma regularize_lower (W : Graphon Ω μ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (a b : Ω) :
    ε ≤ W.regularize ε h0 h1 a b := by
  rw [Graphon.regularize_apply]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr h1) (W.nonneg a b))

/-- Continuity of a product of densities under regularization. -/
lemma abs_prod_cliqueDensity_regularize_le (W : Graphon Ω μ) (f : Fin m → ℕ) (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    |∏ i, cliqueDensity (f i) (W.regularize ε h0 h1) - ∏ i, cliqueDensity (f i) W| ≤
      (∑ i, ((⊤ : SimpleGraph (Fin (f i))).edgeFinset.card : ℝ)) * ε := by
  calc |∏ i, cliqueDensity (f i) (W.regularize ε h0 h1) - ∏ i, cliqueDensity (f i) W|
      ≤ ∑ i, |cliqueDensity (f i) (W.regularize ε h0 h1) - cliqueDensity (f i) W| :=
        abs_finset_prod_sub_prod_le_sum_abs _ _ _
          (fun i _ ↦ cliqueDensity_nonneg _ _) (fun i _ ↦ cliqueDensity_le_one _ _)
          (fun i _ ↦ cliqueDensity_nonneg _ _) (fun i _ ↦ cliqueDensity_le_one _ _)
    _ ≤ ∑ i, ((⊤ : SimpleGraph (Fin (f i))).edgeFinset.card : ℝ) * ε :=
        Finset.sum_le_sum fun i _ ↦ by
          simpa [cliqueDensity] using
            abs_homDensity_regularize_sub_le (⊤ : SimpleGraph (Fin (f i))) W ε h0 h1
    _ = _ := by rw [Finset.sum_mul]

include hk in
/-- **Proposition 2.1**: under `b_1 ≤ ⋯ ≤ b_k`, every graphon satisfies
`∏_i t(K_{r_i},W) ≤ t(H,W) ∏_i t(K_{s_i},W)`. -/
theorem gluing_inequality (hmono : ProfileMonotone D k) (W : Graphon Ω μ) :
    ∏ i, cliqueDensity (r D i) W ≤ homDensity H W * ∏ i, cliqueDensity (s D i) W := by
  apply le_of_regularize W (L := fun V ↦ ∏ i, cliqueDensity (r D i) V)
    (R := fun V ↦ homDensity H V * ∏ i, cliqueDensity (s D i) V)
    (CL := ∑ i, ((⊤ : SimpleGraph (Fin (r D i))).edgeFinset.card : ℝ))
    (CR := (H.edgeFinset.card : ℝ) + ∑ i, ((⊤ : SimpleGraph (Fin (s D i))).edgeFinset.card : ℝ))
  · intro ε h0 h1
    exact abs_prod_cliqueDensity_regularize_le W _ ε h0 h1
  · intro ε h0 h1
    set a := homDensity H (W.regularize ε h0 h1)
    set a' := homDensity H W
    set b := ∏ i, cliqueDensity (s D i) (W.regularize ε h0 h1)
    set b' := ∏ i, cliqueDensity (s D i) W
    have ha := abs_homDensity_regularize_sub_le H W ε h0 h1
    have hb := abs_prod_cliqueDensity_regularize_le W (s D) ε h0 h1
    have hb0 : 0 ≤ b := Finset.prod_nonneg fun i _ ↦ cliqueDensity_nonneg _ _
    have hb1 : b ≤ 1 := Finset.prod_le_one (fun i _ ↦ cliqueDensity_nonneg _ _)
      fun i _ ↦ cliqueDensity_le_one _ _
    have ha'0 : 0 ≤ a' := homDensity_nonneg H W
    have ha'1 : a' ≤ 1 := homDensity_le_one H W
    calc |a * b - a' * b'| = |(a - a') * b + a' * (b - b')| := by ring_nf
      _ ≤ |a - a'| * b + a' * |b - b'| := by
          calc _ ≤ |(a - a') * b| + |a' * (b - b')| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg ha'0]
      _ ≤ |a - a'| * 1 + 1 * |b - b'| := by
          gcongr
      _ ≤ _ := by
          rw [mul_one, one_mul, add_mul]
          exact add_le_add ha hb
  · intro ε h0 h1
    exact gluing_of_lower_bound D k hk hmono _ h0 (regularize_lower W h0.le h1)

/-! ### Lemma 1.2 -/

include hk in
/-- `Φ_H(p) = ∏_i ∏_{s_i ≤ j < r_i} (1 - j(1-p))`. -/
theorem chromaticTarget_profilePoly (p : ℝ) :
    chromaticTarget (V := V) (profilePoly D) p =
      ∏ i, ∏ j ∈ Finset.Ico (s D i) (r D i), cliqueStepFactor (j + 1) p := by
  have hcard := card_eq_sum D k hk
  by_cases hp : p = 1
  · subst hp
    rw [chromaticTarget_at_one]
    simp [cliqueStepFactor]
  · rw [chromaticTarget_of_ne_one _ hp, hcard, profilePoly, Polynomial.eval_prod]
    have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Polynomial.eval_prod, ← Nat.card_Ico, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, cliqueStepFactor,
      Nat.add_sub_cancel]
    field_simp

/-- The Moon–Moser chain `t_a ∏_{a ≤ j < b} (1 - j(1-p)) ≤ t_b` for `a ≤ b ≤ k`. -/
lemma cliqueDensity_mul_prod_step_le (W : Graphon Ω μ) (hk3 : 3 ≤ k)
    (hp : 1 - 1 / (((k - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W) {a b : ℕ} (hab : a ≤ b)
    (hbk : b ≤ k) :
    cliqueDensity a W * ∏ j ∈ Finset.Ico a b, cliqueStepFactor (j + 1) (cliqueDensity 2 W) ≤
      cliqueDensity b W := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.prod_Ico_succ_top hab, ← mul_assoc]
      have hc : 0 ≤ cliqueStepFactor (b + 1) (cliqueDensity 2 W) :=
        cliqueStepFactor_nonneg hk3 hbk hp
      calc cliqueDensity a W * (∏ j ∈ Finset.Ico a b,
            cliqueStepFactor (j + 1) (cliqueDensity 2 W)) *
            cliqueStepFactor (b + 1) (cliqueDensity 2 W)
          ≤ cliqueDensity b W * cliqueStepFactor (b + 1) (cliqueDensity 2 W) :=
            mul_le_mul_of_nonneg_right (ih (by omega)) hc
        _ ≤ cliqueDensity (b + 1) W := by
          rcases Nat.eq_zero_or_pos b with rfl | hb
          · simp [cliqueStepFactor]
          · have := cliqueDensity_step_lower W hk3 hp (j := b + 1) (by omega) hbk
            simpa [mul_comm] using this

include hk in
/-- **Lemma 1.2**: a chordal graph whose clique tree has nondecreasing
profile `b_1 ≤ ⋯ ≤ b_k` (clique number `k ≥ 3`) satisfies the Goodman-type lower
bound. -/
theorem satisfiesLowerBound_of_profile (hk3 : 3 ≤ k) {i₀ : Fin m}
    (hi₀ : (D.bag i₀).card = k) (hmono : ProfileMonotone D k) : SatisfiesLowerBound H := by
  intro P q hP hq Ω _ μ _ W hadm
  have hPeq := IsChromaticPolynomial.unique H hP (isChromaticPolynomial_profilePoly D k hk)
  have hqeq := IsChromaticNumber.unique H hq (isChromaticNumber_of_bags D k hk hi₀)
  subst hPeq hqeq
  have hp : 1 - 1 / (((q - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W := hadm
  rw [chromaticTarget_profilePoly D q hk (edgeDensity W)]
  set p := cliqueDensity 2 W
  set Φ := ∏ i, ∏ j ∈ Finset.Ico (s D i) (r D i), cliqueStepFactor (j + 1) p
  -- per bag, then over the tree
  have hbag : ∀ i, cliqueDensity (s D i) W *
      ∏ j ∈ Finset.Ico (s D i) (r D i), cliqueStepFactor (j + 1) p ≤ cliqueDensity (r D i) W :=
    fun i ↦ cliqueDensity_mul_prod_step_le q W hk3 hp (s_le_r D i) (hk i)
  have hprod : (∏ i, cliqueDensity (s D i) W) * Φ ≤ ∏ i, cliqueDensity (r D i) W := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun i _ ↦ mul_nonneg (cliqueDensity_nonneg _ _)
      (Finset.prod_nonneg fun j hj ↦ cliqueStepFactor_nonneg hk3 ?_ hp)) fun i _ ↦ hbag i
    have := (Finset.mem_Ico.mp hj).2
    have := hk i
    unfold r at *
    omega
  have hglue := gluing_inequality D q hk hmono W
  have hA : 0 < ∏ i, cliqueDensity (s D i) W := by
    refine Finset.prod_pos fun i _ ↦ ?_
    have hslt := s_lt D q hk hk3 i
    exact lt_of_lt_of_le (cliquePoly_pos_of_lt_threshold hk3 hslt hp)
      (cliqueDensity_ge_cliquePoly W hk3 hp hslt.le)
  have : (∏ i, cliqueDensity (s D i) W) * Φ ≤ (∏ i, cliqueDensity (s D i) W) * homDensity H W := by
    rw [mul_comm _ (homDensity H W)]; exact hprod.trans hglue
  exact le_of_mul_le_mul_left this hA

/-- **Lemma 1.2, chordal form**: if `H` is chordal and a maximal-clique
tree of it has nondecreasing profile, then `H` satisfies the Goodman-type lower
bound.  (`k` is the clique number: all bags have size at most `k`, one has size `k`.) -/
theorem chordal_satisfiesLowerBound_of_profile {m : ℕ} (D : MaximalCliqueTreeDecomp H m)
    {k : ℕ} (hk3 : 3 ≤ k) (hk : ∀ i, (D.bag i).card ≤ k) (hmax : ∃ i, (D.bag i).card = k)
    (hmono : ∀ j, 1 ≤ j → j < k → profileB D j ≤ profileB D (j + 1)) :
    SatisfiesLowerBound H := by
  obtain ⟨i₀, hi₀⟩ := hmax
  exact satisfiesLowerBound_of_profile D k hk hk3 hi₀ hmono

/-- **Theorem 1.1 from the criterion**: when every bag has size `k ≥ 3`,
`b_j = m - #{i : s_i ≥ j}` is nondecreasing. -/
theorem pure_profileMonotone {k : ℕ} (hpure : ∀ i, (D.bag i).card = k) : ProfileMonotone D k := by
  intro j hj1 hjk
  unfold profileB
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have := hpure i
  unfold r at *
  omega

end Taeyoung.Paper.Profile
