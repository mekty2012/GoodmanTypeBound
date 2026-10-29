import Taeyoung.Paper.Profile.Extension
import Taeyoung.Paper.Profile.Marginals

/-!
# The gluing inequality for unequal bags (`paper.pdf`, Proposition 2.1)

Let `D` be a maximal-clique tree of `H` with bag sizes `r_i ≤ k` and separator
sizes `s_i`, and let `b_j = #{i : s_i < j ≤ r_i}`.  If `b_1 ≤ b_2 ≤ ⋯ ≤ b_k`, then
for every graphon

```
∏_i t(K_{r_i}, W) ≤ t(H, W) · ∏_i t(K_{s_i}, W)                     (gluing)
```

(`gluing_inequality`).  Since `∏_i t_{r_i} / ∏_i t_{s_i} = t_k^{b_k} ∏_{j<k} t_j^{b_j - b_{j+1}}`,
this is the paper's `t(H,W) ∏_{j<k} t_j^{b_{j+1}-b_j} ≥ t_k^{b_k}`.

**The proof** follows the paper, on the padded pure tree `D' = extDecomp D k`
(`Paper/Profile/Extension.lean`), for a graphon bounded below by `δ > 0`:

* `Q` is the junction law of `D'`; every bag marginal of `Q` is `κ_k/t_k`, so its
  marginal on `C_i` is the paper's law of `(X_1, …, X_{r_i})` (`integral_junction_mul`).
* The comparison law is `G = (κ_H/t(H)) ∏_i κ_{C'_i}/m_i(C_i)`: the graph law on the
  original coordinates, extended to the padding of each bag by the conditional law
  of `ρ_k`.  It is a probability density (`lintegral_refENN`).
* Gibbs, `∫ Q log(G/Q) ≤ 0`, together with `κ_H ∏ κ_{S_i} = ∏ κ_{C_i}`, gives
  `log t(H) ≥ ∑_i E_Q[φ(C_i)] - ∑_i E_Q[φ(S_i)]`, where
  `φ(A) = log κ_A - log m(A)` and `m(A)` is the bag marginal on `A`.
* By exchangeability, `E_Q[φ(A)] = γ_{|A|}` depends only on `|A|`, and by Gibbs on
  one bag, `γ_j ≤ log t_j - log t_k` with equality at `j = 0` and `j = k`.
  Abel summation and `b_j ≤ b_{j+1}` then bound the right side below by
  `∑_i (log t_{r_i} - log t_{s_i})`.

The regularization `W_ε = ε + (1-ε)W` removes the lower bound (`gluing_inequality`).
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Taeyoung.Paper.Profile

open Taeyoung Taeyoung.Methods.PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
  {m : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The profile -/

/-- `b_j = #{i : s_i < j ≤ r_i}`, the multiplicity of `j - 1` as a root of `P_H`. -/
def profileB (D : MaximalCliqueTreeDecomp H m) (j : ℕ) : ℕ :=
  (univ.filter fun i : Fin m ↦ s D i < j ∧ j ≤ r D i).card

/-- The paper's form `b_j = #{i : r_i ≥ j} - #{e : s_e ≥ j}`. -/
lemma profileB_eq_sub (D : MaximalCliqueTreeDecomp H m) (j : ℕ) :
    (profileB D j : ℤ) = (univ.filter fun i : Fin m ↦ j ≤ r D i).card -
      (univ.filter fun i : Fin m ↦ j ≤ s D i).card := by
  have hsub : (univ.filter fun i : Fin m ↦ j ≤ s D i) ⊆
      (univ.filter fun i : Fin m ↦ j ≤ r D i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans (s_le_r D i)
  have hdiff : (univ.filter fun i : Fin m ↦ s D i < j ∧ j ≤ r D i) =
      (univ.filter fun i : Fin m ↦ j ≤ r D i) \ (univ.filter fun i : Fin m ↦ j ≤ s D i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_le]
    tauto
  rw [profileB, hdiff, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]

/-- The monotonicity hypothesis of Lemma 1.2. -/
def ProfileMonotone (D : MaximalCliqueTreeDecomp H m) (k : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j < k → profileB D j ≤ profileB D (j + 1)

/-! ### Algebra: telescoping and Abel summation -/

lemma sum_Ico_telescope (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, (f (j + 1) - f j) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, ih]
      ring

/-- Swapping the bag sum and the level sum. -/
lemma sum_bags_telescope (D : MaximalCliqueTreeDecomp H m) {k : ℕ}
    (hk : ∀ i, r D i ≤ k) (f : ℕ → ℝ) :
    ∑ i : Fin m, (f (r D i) - f (s D i)) =
      ∑ j ∈ Finset.range k, (profileB D (j + 1) : ℝ) * (f (j + 1) - f j) := by
  have h1 : ∀ i : Fin m, f (r D i) - f (s D i) =
      ∑ j ∈ Finset.range k, if s D i ≤ j ∧ j < r D i then f (j + 1) - f j else 0 := by
    intro i
    rw [← sum_Ico_telescope f (s_le_r D i), ← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by have := hk i; omega, h1, h2⟩
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, profileB]
  have hset : (univ.filter fun i : Fin m ↦ s D i ≤ j ∧ j < r D i) =
      univ.filter fun i : Fin m ↦ s D i < j + 1 ∧ j + 1 ≤ r D i :=
    Finset.filter_congr fun i _ ↦ by omega
  rw [hset]

/-- **Abel summation**: with `δ ≥ 0`, `δ_0 = δ_k = 0` and `b` nondecreasing on
`[1,k]`, the sum `∑_{j<k} b_{j+1}(δ_{j+1} - δ_j)` is nonpositive. -/
lemma abel_nonpos (k : ℕ) (b : ℕ → ℕ) (δ : ℕ → ℝ) (hδ0 : δ 0 = 0) (hδk : δ k = 0)
    (hδ : ∀ j, 0 ≤ δ j) (hb : ∀ j, 1 ≤ j → j < k → b j ≤ b (j + 1)) :
    ∑ j ∈ Finset.range k, (b (j + 1) : ℝ) * (δ (j + 1) - δ j) ≤ 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have key : ∀ n, 1 ≤ n → n ≤ k →
      ∑ j ∈ Finset.range n, (b (j + 1) : ℝ) * (δ (j + 1) - δ j) ≤ b n * δ n := by
    intro n hn hnk
    induction n, hn using Nat.le_induction with
    | base => simp [hδ0]
    | succ n hn ih =>
        rw [Finset.sum_range_succ]
        have ih' := ih (by omega)
        have hbn : (b n : ℝ) ≤ b (n + 1) := by exact_mod_cast hb n hn (by omega)
        have := hδ n
        nlinarith
  have := key k hk le_rfl
  rw [hδk, mul_zero] at this
  exact this

/-! ### The padded tree and its laws -/

variable (D : MaximalCliqueTreeDecomp H m) (k : ℕ) (hk : ∀ i, (D.bag i).card ≤ k)

/-- `C_i`, as a subset of the padded vertex set. -/
def liftBag (i : Fin m) : Finset (ExtV D k) := (D.bag i).disjSum ∅

/-- `S_i`, as a subset of the padded vertex set. -/
def liftSep (i : Fin m) : Finset (ExtV D k) := (sep D i).disjSum ∅

lemma liftBag_subset (i : Fin m) : liftBag D k i ⊆ extBag D k i := by
  intro x hx
  rcases x with v | e
  · simpa [liftBag] using hx
  · simp [liftBag] at hx

lemma liftSep_subset (i : Fin m) : liftSep D k i ⊆ extBag D k i := by
  intro x hx
  rcases x with v | e
  · simp only [liftSep, Finset.inl_mem_disjSum] at hx
    simpa using sep_subset_bag D i hx
  · simp [liftSep] at hx

lemma card_liftBag (i : Fin m) : (liftBag D k i).card = r D i := by
  simp [liftBag, r]

lemma card_liftSep (i : Fin m) : (liftSep D k i).card = s D i := by
  simp [liftSep, s]

lemma extDecomp_separator_eq (i : Fin m) :
    (extDecomp D k hk).separator i = liftSep D k i :=
  extDecomp_separator D k hk i

/-- The separator marginal of the padded tree is the marginal on `S_i`. -/
lemma bagNewMarginalENN_eq_margOn (W : Graphon Ω μ) (i : Fin m) :
    (extDecomp D k hk).bagNewMarginalENN W i = margOn W (extBag D k i) (liftSep D k i) := by
  unfold PureCliqueTreeDecomp.bagNewMarginalENN PureCliqueTreeDecomp.newVertices margOn
    PureCliqueTreeDecomp.bagWeightENN
  rw [extDecomp_separator_eq]
  rfl

variable {δ : ℝ}

lemma normalizedBagENN_toReal (W : Graphon Ω μ) (i : Fin m) (x : ExtV D k → Ω) :
    ((extDecomp D k hk).normalizedBagENN W i x).toReal = nb W (extBag D k i) x := by
  unfold PureCliqueTreeDecomp.normalizedBagENN PureCliqueTreeDecomp.cliqueMassENN
    PureCliqueTreeDecomp.bagWeightENN cliqueWeightOnENN nb
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (cliqueDensity_nonneg _ W),
    ENNReal.toReal_ofReal (cliqueWeightOn_nonneg _ W x), card_extBag hk, div_eq_mul_inv,
    mul_comm]
  rfl

/-- **Bag marginals of the junction law**: against a bounded test function of the
coordinates of `C'_i`, `Q` integrates like `ρ_{C'_i}`. -/
theorem integral_junction_mul (W : Graphon Ω μ) (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (i : Fin m) {F : (ExtV D k → Ω) → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ x, |F x| ≤ C)
    (hFdep : ∀ ⦃x y : ExtV D k → Ω⦄, (∀ v ∈ extBag D k i, x v = y v) → F x = F y) :
    ∫ x, (extDecomp D k hk).junctionDensity W x * F x ∂Measure.pi (fun _ : ExtV D k ↦ μ) =
      ∫ x, nb W (extBag D k i) x * F x ∂Measure.pi (fun _ : ExtV D k ↦ μ) := by
  classical
  set D' := extDecomp D k hk
  haveI := nonempty_of_isProbabilityMeasure μ
  obtain ⟨ω⟩ := this
  let x₀ : ExtV D k → Ω := fun _ ↦ ω
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hFC x₀)
  -- shift to a nonnegative test function
  let G : (ExtV D k → Ω) → ℝ := fun x ↦ F x + C
  have hG0 : ∀ x, 0 ≤ G x := fun x ↦ by
    have := (abs_le.mp (hFC x)).1; simp only [G]; linarith
  have hGm : Measurable G := hF.add_const C
  have hGdep : FinsetDependsOn (extBag D k i) fun x ↦ ENNReal.ofReal (G x) := fun x y hxy ↦ by
    simp only [G, hFdep hxy]
  have hmargQ : lmarginal (fun _ : ExtV D k ↦ μ) (univ \ extBag D k i)
      (D'.partialJunctionENN W m) = D'.normalizedBagENN W i :=
    D'.partialJunctionENN_bagMarginal W hδpos hδ m le_rfl i i.2
  have hmargN : lmarginal (fun _ : ExtV D k ↦ μ) (univ \ extBag D k i)
      (D'.normalizedBagENN W i) = D'.normalizedBagENN W i :=
    D'.lmarginal_normalizedBagENN_compl W i
  have hlin := lintegral_mul_eq_of_lmarginal_eq (μ := μ) x₀
    (D'.measurable_partialJunctionENN W m) (D'.measurable_normalizedBagENN W i)
    hGm.ennreal_ofReal hGdep (by rw [hmargQ, hmargN])
  -- convert to real integrals
  have hQ0 : ∀ x, 0 ≤ D'.junctionDensity W x := fun x ↦ ENNReal.toReal_nonneg
  have hN0 : ∀ x, 0 ≤ nb W (extBag D k i) x := fun x ↦
    div_nonneg (cliqueWeightOn_nonneg _ W x) (cliqueDensity_nonneg _ W)
  obtain ⟨bQ, hbQ, hQb⟩ := D'.junctionDensity_exists_upper_bound W hδpos hδ
  have hNpos := cliqueDensity_pos' W hδpos hδ (extBag D k i).card
  have hNb : ∀ x, nb W (extBag D k i) x ≤ 1 / cliqueDensity (extBag D k i).card W := fun x ↦
    div_le_div_of_nonneg_right (cliqueWeightOn_le_one _ W x) hNpos.le
  have hGC : ∀ x, G x ≤ 2 * C := fun x ↦ by
    have := (abs_le.mp (hFC x)).2; simp only [G]; linarith
  have hQm := D'.measurable_junctionDensity W
  have hNm := measurable_nb W (extBag D k i)
  have hQint : Integrable (D'.junctionDensity W) (Measure.pi fun _ : ExtV D k ↦ μ) :=
    integrable_of_bounded hQm bQ fun x ↦ by rw [abs_of_nonneg (hQ0 x)]; exact hQb x
  have hNint : Integrable (nb W (extBag D k i)) (Measure.pi fun _ : ExtV D k ↦ μ) :=
    integrable_of_bounded hNm _ fun x ↦ by rw [abs_of_nonneg (hN0 x)]; exact hNb x
  have hQGint : Integrable (fun x ↦ D'.junctionDensity W x * G x)
      (Measure.pi fun _ : ExtV D k ↦ μ) :=
    integrable_of_bounded (hQm.mul hGm) (bQ * (2 * C)) fun x ↦ by
      rw [abs_of_nonneg (mul_nonneg (hQ0 x) (hG0 x))]
      exact mul_le_mul (hQb x) (hGC x) (hG0 x) hbQ.le
  have hNGint : Integrable (fun x ↦ nb W (extBag D k i) x * G x)
      (Measure.pi fun _ : ExtV D k ↦ μ) :=
    integrable_of_bounded (hNm.mul hGm) (1 / cliqueDensity (extBag D k i).card W * (2 * C))
      fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (hN0 x) (hG0 x))]
        exact mul_le_mul (hNb x) (hGC x) (hG0 x) (by positivity)
  have hQFint : Integrable (fun x ↦ D'.junctionDensity W x * F x)
      (Measure.pi fun _ : ExtV D k ↦ μ) :=
    integrable_of_bounded (hQm.mul hF) (bQ * C) fun x ↦ by
      rw [abs_mul, abs_of_nonneg (hQ0 x)]
      exact mul_le_mul (hQb x) (hFC x) (abs_nonneg _) hbQ.le
  have hNFint : Integrable (fun x ↦ nb W (extBag D k i) x * F x)
      (Measure.pi fun _ : ExtV D k ↦ μ) :=
    integrable_of_bounded (hNm.mul hF) (1 / cliqueDensity (extBag D k i).card W * C)
      fun x ↦ by
        rw [abs_mul, abs_of_nonneg (hN0 x)]
        exact mul_le_mul (hNb x) (hFC x) (abs_nonneg _) (by positivity)
  have hreal : ∫ x, D'.junctionDensity W x * G x ∂Measure.pi (fun _ : ExtV D k ↦ μ) =
      ∫ x, nb W (extBag D k i) x * G x ∂Measure.pi (fun _ : ExtV D k ↦ μ) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ mul_nonneg (hQ0 x) (hG0 x))
        hQGint.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ mul_nonneg (hN0 x) (hG0 x))
        hNGint.aestronglyMeasurable]
    congr 1
    have e1 : (fun x ↦ ENNReal.ofReal (D'.junctionDensity W x * G x)) =
        fun x ↦ D'.partialJunctionENN W m x * ENNReal.ofReal (G x) := by
      funext x
      rw [ENNReal.ofReal_mul (hQ0 x), PureCliqueTreeDecomp.junctionDensity,
        ENNReal.ofReal_toReal (D'.partialJunctionENN_ne_top W hδpos hδ m x)]
    have e2 : (fun x ↦ ENNReal.ofReal (nb W (extBag D k i) x * G x)) =
        fun x ↦ D'.normalizedBagENN W i x * ENNReal.ofReal (G x) := by
      funext x
      rw [ENNReal.ofReal_mul (hN0 x), ← normalizedBagENN_toReal D k hk W i x,
        ENNReal.ofReal_toReal]
      exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (D'.cliqueMassENN_ne_zero W hδpos hδ))
        (D'.bagWeightENN_ne_top W i x)
    rw [e1, e2]
    exact hlin
  -- undo the shift
  have hQ1 := D'.integral_junctionDensity_eq_one W hδpos hδ
  have hN1 : ∫ x, nb W (extBag D k i) x ∂Measure.pi (fun _ : ExtV D k ↦ μ) = 1 := by
    unfold nb
    rw [integral_div]
    have := integral_cliqueWeightOn (μ := μ) (extBag D k i) W
    simp only [assignmentMeasure] at this
    rw [this]
    exact div_self hNpos.ne'
  have hQF : ∫ x, D'.junctionDensity W x * G x ∂Measure.pi (fun _ : ExtV D k ↦ μ) =
      ∫ x, D'.junctionDensity W x * F x ∂Measure.pi (fun _ : ExtV D k ↦ μ) + C := by
    calc ∫ x, D'.junctionDensity W x * G x ∂Measure.pi (fun _ : ExtV D k ↦ μ) =
          ∫ x, (D'.junctionDensity W x * F x + D'.junctionDensity W x * C)
            ∂Measure.pi (fun _ : ExtV D k ↦ μ) := by
          congr 1; funext x; simp only [G]; ring
      _ = _ := by rw [integral_add hQFint (hQint.mul_const C), integral_mul_const, hQ1, one_mul]
  have hNF : ∫ x, nb W (extBag D k i) x * G x ∂Measure.pi (fun _ : ExtV D k ↦ μ) =
      ∫ x, nb W (extBag D k i) x * F x ∂Measure.pi (fun _ : ExtV D k ↦ μ) + C := by
    calc ∫ x, nb W (extBag D k i) x * G x ∂Measure.pi (fun _ : ExtV D k ↦ μ) =
          ∫ x, (nb W (extBag D k i) x * F x + nb W (extBag D k i) x * C)
            ∂Measure.pi (fun _ : ExtV D k ↦ μ) := by
          congr 1; funext x; simp only [G]; ring
      _ = _ := by rw [integral_add hNFint (hNint.mul_const C), integral_mul_const, hN1, one_mul]
  linarith

end Taeyoung.Paper.Profile
