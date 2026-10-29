import Taeyoung.Paper.Eventual.L2
import Taeyoung.Paper.Eventual.Leaves

/-!
# Forest densities (`paper.pdf`, Lemmas 4.4, 4.5)

Lemma 4.3 is not formalized; leaf integration replaces it.  All three
statements below are proved by integrating leaves (`wInt_leaf`):

* `wInt_forest_const`: if the degree function is the constant `q`, a forest
  with `r` edges has density `q^r` (used for the block graphon in the forest
  form of the chromatic polynomial);
* `forest_variance`: **Lemma 4.4** as the absolute bound
  `|t(F,U) - q^r| ≤ C(r,2) Δ^{r-2} X` (the sign `t(F,U) ≥ q^r` in
  (4.8) is not proved here), in the weighted form carried
  by `GoodWeight` and multiplied by `Δ²`;
* `wInt_prune`: integrating the leaves of a forest `F'` that hang off a vertex
  set `R` costs a factor `Δ` per edge.  This is the leaf-integration step of
  Lemma 4.5, and gives `t(F,U) ≤ Δ^{|F|}`.
-/

open MeasureTheory Finset

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Small facts about products and sums -/

/-- Telescoping a product difference. -/
lemma abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b M : ι → ℝ)
    (hM : ∀ i ∈ s, 0 ≤ M i) (ha : ∀ i ∈ s, |a i| ≤ M i) (hb : ∀ i ∈ s, |b i| ≤ M i) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| * ∏ j ∈ s.erase i, M j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    have hMe := hM e (mem_insert_self e s)
    have hae := ha e (mem_insert_self e s)
    have hbe := hb e (mem_insert_self e s)
    have ih' := ih (fun i hi ↦ hM i (mem_insert_of_mem hi))
      (fun i hi ↦ ha i (mem_insert_of_mem hi)) (fun i hi ↦ hb i (mem_insert_of_mem hi))
    have hbs : |∏ i ∈ s, b i| ≤ ∏ i ∈ s, M i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) fun i hi ↦ hb i (mem_insert_of_mem hi)
    rw [prod_insert he, prod_insert he, sum_insert he, erase_insert he]
    have hsplit : a e * ∏ i ∈ s, a i - b e * ∏ i ∈ s, b i =
        a e * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i) + (a e - b e) * ∏ i ∈ s, b i := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |a e| * |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤
        M e * ∑ i ∈ s, |a i - b i| * ∏ j ∈ s.erase i, M j :=
      mul_le_mul hae ih' (abs_nonneg _) hMe
    have h2 : |a e - b e| * |∏ i ∈ s, b i| ≤ |a e - b e| * ∏ i ∈ s, M i :=
      mul_le_mul_of_nonneg_left hbs (abs_nonneg _)
    have h3 : M e * ∑ i ∈ s, |a i - b i| * ∏ j ∈ s.erase i, M j =
        ∑ i ∈ s, |a i - b i| * ∏ j ∈ (insert e s).erase i, M j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hie : i ≠ e := fun h ↦ he (h ▸ hi)
      rw [erase_insert_of_ne (Ne.symm hie), prod_insert (fun h ↦ he (mem_of_mem_erase h))]
      ring
    linarith

/-- `∑ C(k_v,2) ≤ C(∑ k_v, 2)`. -/
lemma sum_choose_two_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (k : ι → ℕ) :
    ∑ i ∈ s, ((k i).choose 2 : ℝ) ≤ ((∑ i ∈ s, k i).choose 2 : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    rw [sum_insert he, sum_insert he]
    have hcast : (((k e + ∑ i ∈ s, k i).choose 2 : ℕ) : ℝ) =
        (k e).choose 2 + (∑ i ∈ s, k i).choose 2 + (k e : ℝ) * (∑ i ∈ s, k i : ℕ) := by
      rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
      push_cast; ring
    rw [hcast]
    have : (0 : ℝ) ≤ (k e : ℝ) * (∑ i ∈ s, k i : ℕ) := by positivity
    linarith

/-! ### Constant degree -/

/-- **Forests in a graphon of constant degree.** -/
theorem wInt_forest_const (U : Graphon Ω μ) {q : ℝ} (hq : ∀ x, degree U x = q) :
    ∀ (n : ℕ) (F : Finset (Sym2 V)), F.card = n → IsForest F → (∀ e ∈ F, ¬ e.IsDiag) →
      ∀ c : V → ℝ, wInt (fun _ ↦ U) F (fun v ↦ BddFun.const (c v)) = q ^ F.card * ∏ v, c v := by
  intro n
  induction n with
  | zero =>
    intro F hF _ _ c
    rw [Finset.card_eq_zero.mp hF, wInt_empty]
    simp
  | succ n ih =>
    intro F hF hfor hnd c
    obtain ⟨ℓ, u, hℓu, he, honly⟩ :=
      exists_leaf hfor hnd (Finset.card_pos.mp (by omega))
    rw [wInt_leaf _ F _ hℓu he honly]
    set c' : V → ℝ := Function.update (Function.update c ℓ 1) u (c u * (c ℓ * q))
    have hw : ∀ v y, (Function.update (Function.update (fun v ↦ BddFun.const (c v)) ℓ
        BddFun.one) u ((BddFun.const (c u)).mul
          (BddFun.apply U (BddFun.const (c ℓ))))) v y = BddFun.const (c' v) y := by
      intro v y
      by_cases hvu : v = u
      · subst hvu
        simp only [Function.update_self, BddFun.mul_apply, BddFun.const_apply,
          BddFun.apply_apply, c']
        rw [integral_mul_const]
        rw [show (∫ z, U y z ∂μ) = q from hq y]
        ring
      · by_cases hvℓ : v = ℓ
        · subst hvℓ
          simp [Function.update_of_ne hvu, c', BddFun.one]
        · simp [Function.update_of_ne hvu, Function.update_of_ne hvℓ, c']
    rw [wInt_congr_weight _ _ hw]
    have hcard : (F.erase s(ℓ, u)).card = n := by
      rw [Finset.card_erase_of_mem he]; omega
    rw [ih _ hcard (hfor.subset (erase_subset _ _))
      (fun e he' ↦ hnd e (mem_of_mem_erase he')) c', Finset.card_erase_of_mem he]
    have hprod : ∏ v, c' v = q * ∏ v, c v := by
      have hℓ : ℓ ∈ univ \ {u} := by simp [hℓu]
      rw [Finset.prod_update_of_mem (mem_univ u), Finset.prod_update_of_mem hℓ,
        ← Finset.mul_prod_erase univ c (mem_univ u)]
      have : (univ.erase u) = univ \ {u} := (Finset.sdiff_singleton_eq_erase u univ).symm
      rw [this, ← Finset.mul_prod_erase (univ \ {u}) c hℓ]
      have h2 : (univ \ {u}).erase ℓ = (univ \ {u}) \ {ℓ} :=
        (Finset.sdiff_singleton_eq_erase ℓ _).symm
      rw [h2]
      ring
    rw [hprod, hF]
    simp only [Nat.add_sub_cancel]
    ring

/-! ### Lemma 4.4 -/

/-- **Lemma 4.4, weighted form.**  If every vertex weight `φ_v` has
absorbed `k_v` edges, then with `N = |F| + ∑ k_v`,
`Δ² |∫ ∏_F U ∏ φ - q^N| ≤ C(N,2) Δ^N X`. -/
theorem forest_variance (U : Graphon Ω μ) {Δ : ℝ} (hΔ : 0 < Δ) (hdeg : ∀ x, degree U x ≤ Δ) :
    ∀ (n : ℕ) (F : Finset (Sym2 V)), F.card = n → IsForest F → (∀ e ∈ F, ¬ e.IsDiag) →
      ∀ (φ : V → BddFun Ω) (k : V → ℕ), (∀ v, GoodWeight U Δ (k v) (φ v)) →
        Δ ^ 2 * |wInt (fun _ ↦ U) F φ - meanDeg U ^ (F.card + ∑ v, k v)| ≤
          ((F.card + ∑ v, k v).choose 2 : ℝ) * Δ ^ (F.card + ∑ v, k v) * degVar U := by
  intro n
  induction n with
  | zero =>
    intro F hF _ _ φ k hk
    rw [Finset.card_eq_zero.mp hF, wInt_empty, Finset.card_empty, zero_add]
    rw [← Finset.prod_pow_eq_pow_sum]
    have htel := abs_prod_sub_prod_le univ (fun v ↦ ∫ y, φ v y ∂μ)
      (fun v ↦ meanDeg U ^ k v) (fun v ↦ Δ ^ k v) (fun v _ ↦ pow_nonneg hΔ.le _)
      (fun v _ ↦ (hk v).abs_integral_le)
      (fun v _ ↦ by
        rw [abs_of_nonneg (pow_nonneg (meanDeg_nonneg U) _)]
        exact pow_le_pow_left₀ (meanDeg_nonneg U) (meanDeg_le U hdeg) _)
    calc Δ ^ 2 * |∏ v, ∫ y, φ v y ∂μ - ∏ v, meanDeg U ^ k v|
        ≤ Δ ^ 2 * ∑ v, |∫ y, φ v y ∂μ - meanDeg U ^ k v| * ∏ w ∈ univ.erase v, Δ ^ k w :=
          mul_le_mul_of_nonneg_left htel (sq_nonneg _)
      _ = ∑ v, (Δ ^ 2 * |∫ y, φ v y ∂μ - meanDeg U ^ k v|) * ∏ w ∈ univ.erase v, Δ ^ k w := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ ↦ by ring
      _ ≤ ∑ v, ((k v).choose 2 * Δ ^ k v * degVar U) * ∏ w ∈ univ.erase v, Δ ^ k w := by
          refine Finset.sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_right (hk v).mean_le
            (Finset.prod_nonneg fun w _ ↦ pow_nonneg hΔ.le _)
      _ = ∑ v, ((k v).choose 2 : ℝ) * (Δ ^ (∑ w, k w) * degVar U) := by
          refine Finset.sum_congr rfl fun v _ ↦ ?_
          rw [← Finset.prod_pow_eq_pow_sum,
            ← Finset.mul_prod_erase univ (fun w ↦ Δ ^ k w) (mem_univ v)]
          ring
      _ = (∑ v, ((k v).choose 2 : ℝ)) * (Δ ^ (∑ w, k w) * degVar U) := by
          rw [Finset.sum_mul]
      _ ≤ ((∑ v, k v).choose 2 : ℝ) * (Δ ^ (∑ w, k w) * degVar U) :=
          mul_le_mul_of_nonneg_right (sum_choose_two_le univ k)
            (mul_nonneg (pow_nonneg hΔ.le _) (degVar_nonneg U))
      _ = _ := by ring
  | succ n ih =>
    intro F hF hfor hnd φ k hk
    obtain ⟨ℓ, u, hℓu, he, honly⟩ :=
      exists_leaf hfor hnd (Finset.card_pos.mp (by omega))
    rw [wInt_leaf _ F _ hℓu he honly]
    set φ' := Function.update (Function.update φ ℓ BddFun.one) u
      ((φ u).mul (BddFun.apply U (φ ℓ))) with hφ'
    set k' : V → ℕ := Function.update (Function.update k ℓ 0) u (k u + k ℓ + 1) with hk'
    have hgood : ∀ v, GoodWeight U Δ (k' v) (φ' v) := by
      intro v
      by_cases hvu : v = u
      · subst hvu
        rw [hφ', hk', Function.update_self, Function.update_self]
        exact (hk v).step hΔ hdeg (hk ℓ)
      · rw [hφ', hk', Function.update_of_ne hvu, Function.update_of_ne hvu]
        by_cases hvℓ : v = ℓ
        · subst hvℓ
          rw [Function.update_self, Function.update_self]
          exact goodWeight_one U Δ
        · rw [Function.update_of_ne hvℓ, Function.update_of_ne hvℓ]
          exact hk v
    have hcard : (F.erase s(ℓ, u)).card = n := by
      rw [Finset.card_erase_of_mem he]; omega
    have hsum : ∑ v, k' v = ∑ v, k v + 1 := by
      have hℓ : ℓ ∈ univ \ {u} := by simp [hℓu]
      rw [hk', Finset.sum_update_of_mem (mem_univ u), Finset.sum_update_of_mem hℓ,
        ← Finset.add_sum_erase univ k (mem_univ u)]
      have : (univ.erase u) = univ \ {u} := (Finset.sdiff_singleton_eq_erase u univ).symm
      rw [this, ← Finset.add_sum_erase (univ \ {u}) k hℓ]
      have h2 : (univ \ {u}).erase ℓ = (univ \ {u}) \ {ℓ} :=
        (Finset.sdiff_singleton_eq_erase ℓ _).symm
      rw [h2]
      ring
    have hN : (F.erase s(ℓ, u)).card + ∑ v, k' v = F.card + ∑ v, k v := by
      rw [hsum, hcard, hF]; ring
    have := ih _ hcard (hfor.subset (erase_subset _ _))
      (fun e he' ↦ hnd e (mem_of_mem_erase he')) φ' k' hgood
    rw [hN] at this
    exact this

/-- **Lemma 4.4** for unweighted forests:
`Δ² |t(F,U) - q^r| ≤ C(r,2) Δ^r X`. -/
theorem forest_variance_unweighted (U : Graphon Ω μ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hdeg : ∀ x, degree U x ≤ Δ) {F : Finset (Sym2 V)} (hfor : IsForest F)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) :
    Δ ^ 2 * |wInt (fun _ ↦ U) F (fun _ ↦ BddFun.one) - meanDeg U ^ F.card| ≤
      (F.card.choose 2 : ℝ) * Δ ^ F.card * degVar U := by
  have := forest_variance U hΔ hdeg F.card F rfl hfor hnd (fun _ ↦ BddFun.one) (fun _ ↦ 0)
    (fun _ ↦ goodWeight_one U Δ)
  simpa using this

/-! ### Pruning leaves off a vertex set -/

/-- A vertex on no edge integrates out. -/
lemma wInt_isolated (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V)) (φ : V → BddFun Ω)
    {v : V} (hv : ∀ e ∈ S, v ∉ e) :
    wInt κ S φ = (∫ y, φ v y ∂μ) * wInt κ S (Function.update φ v BddFun.one) := by
  unfold wInt
  rw [integral_update v (measurable_integrand κ S φ) (abs_integrand_le κ S φ),
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only []
  simp_rw [edgeProd_update_of_notMem κ x hv]
  unfold vertexProd
  have h1 : ∀ y, ∏ w, φ w (Function.update x v y w) =
      φ v y * ∏ w ∈ univ.erase v, φ w (x w) := by
    intro y
    rw [prod_univ_eq_mul_erase _ v, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun w hw ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  have h2 : ∏ w, (Function.update φ v BddFun.one) w (x w) = ∏ w ∈ univ.erase v, φ w (x w) := by
    rw [prod_univ_eq_mul_erase _ v, Function.update_self]
    simp only [BddFun.one_apply, one_mul]
    exact Finset.prod_congr rfl fun w hw ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  simp_rw [h1, h2]
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []
  ring

/-- Several isolated vertices integrate out. -/
lemma wInt_isolated_finset (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V)) :
    ∀ (T : Finset V) (φ : V → BddFun Ω), (∀ v ∈ T, ∀ e ∈ S, v ∉ e) →
      wInt κ S φ = (∏ v ∈ T, ∫ y, φ v y ∂μ) *
        wInt κ S (fun v ↦ if v ∈ T then BddFun.one else φ v) := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro φ _; simp
  | @insert a T ha ih =>
    intro φ hT
    rw [ih φ (fun v hv ↦ hT v (mem_insert_of_mem hv)), prod_insert ha]
    rw [wInt_isolated κ S _ (v := a) (hT a (mem_insert_self a T))]
    rw [if_neg ha]
    have hw : wInt κ S (Function.update (fun v ↦ if v ∈ T then BddFun.one else φ v) a
        BddFun.one) = wInt κ S (fun v ↦ if v ∈ insert a T then BddFun.one else φ v) := by
      apply wInt_congr_weight
      intro v y
      by_cases hva : v = a
      · subst hva; simp
      · rw [Function.update_of_ne hva]
        simp [hva]
    rw [hw]
    ring

/-- **Pruning.**  Let `F' ⊆ S` be a forest of `U`-edges hanging off a vertex set
`R`: no two vertices of `R` are joined in `F'`, and every other edge of `S` lies
inside `R`.  If the weights off `R` are bounded by `b`, then
`wInt κ S φ ≤ Δ^{|F'|} ∏_{v ∉ R} b_v · wInt κ (S \ F') φ|_R`. -/
theorem wInt_prune (U : Graphon Ω μ) {Δ : ℝ} (hΔ0 : 0 ≤ Δ) (hdeg : ∀ x, degree U x ≤ Δ)
    (κ : Sym2 V → Graphon Ω μ) (R : Finset V) :
    ∀ (n : ℕ) (S F' : Finset (Sym2 V)), F'.card = n → F' ⊆ S → (∀ e ∈ F', κ e = U) →
      IsForest F' → (∀ e ∈ F', ¬ e.IsDiag) →
      (∀ r₁ ∈ R, ∀ r₂ ∈ R, (graphOf F').Reachable r₁ r₂ → r₁ = r₂) →
      (∀ e ∈ S \ F', ∀ v ∈ e, v ∈ R) →
      ∀ (φ : V → BddFun Ω) (b : V → ℝ), (∀ v y, 0 ≤ φ v y) → (∀ v, 0 ≤ b v) →
        (∀ v, v ∉ R → ∀ y, φ v y ≤ b v) →
        wInt κ S φ ≤ Δ ^ F'.card * (∏ v ∈ univ \ R, b v) *
          wInt κ (S \ F') (fun v ↦ if v ∈ R then φ v else BddFun.one) := by
  intro n
  induction n with
  | zero =>
    intro S F' hF' _ _ _ _ _ hout φ b hφ0 hb0 hb
    rw [Finset.card_eq_zero.mp hF', sdiff_empty, Finset.card_empty, pow_zero, one_mul]
    have hiso : ∀ v ∈ univ \ R, ∀ e ∈ S, v ∉ e := by
      intro v hv e he hve
      have := hout e (by simpa [Finset.card_eq_zero.mp hF'] using he) v hve
      exact (Finset.mem_sdiff.mp hv).2 this
    rw [wInt_isolated_finset κ S (univ \ R) φ hiso]
    have hcongr : wInt κ S (fun v ↦ if v ∈ univ \ R then BddFun.one else φ v) =
        wInt κ S (fun v ↦ if v ∈ R then φ v else BddFun.one) := by
      apply wInt_congr_weight
      intro v y
      by_cases hv : v ∈ R <;> simp [hv]
    rw [hcongr]
    refine mul_le_mul_of_nonneg_right ?_ (wInt_nonneg κ S fun v y ↦ by
      by_cases hv : v ∈ R <;> simp [hv, hφ0, BddFun.one])
    refine Finset.prod_le_prod (fun v _ ↦ integral_nonneg (hφ0 v)) fun v hv ↦ ?_
    calc ∫ y, φ v y ∂μ ≤ ∫ _y, b v ∂μ :=
          integral_mono (φ v).integrable (integrable_const _)
            (hb v (Finset.mem_sdiff.mp hv).2)
      _ = b v := by simp
  | succ n ih =>
    intro S F' hF' hsub hκ hfor hnd hsep hout φ b hφ0 hb0 hb
    obtain ⟨ℓ, u, hℓR, hℓu, he, honly⟩ :=
      exists_leaf_notMem hfor hnd (Finset.card_pos.mp (by omega)) (R : Set V)
        (fun r₁ h₁ r₂ h₂ h ↦ hsep r₁ h₁ r₂ h₂ h)
    replace hℓR : ℓ ∉ R := by simpa using hℓR
    have heS : s(ℓ, u) ∈ S := hsub he
    have honlyS : ∀ e ∈ S, ℓ ∈ e → e = s(ℓ, u) := by
      intro e heS' hℓe
      by_cases heF : e ∈ F'
      · exact honly e heF hℓe
      · exact absurd (hout e (Finset.mem_sdiff.mpr ⟨heS', heF⟩) ℓ hℓe) hℓR
    rw [wInt_leaf κ S φ hℓu heS honlyS, hκ _ he]
    have hcard : (F'.erase s(ℓ, u)).card = n := by
      rw [Finset.card_erase_of_mem he]; omega
    have hsub' : F'.erase s(ℓ, u) ⊆ S.erase s(ℓ, u) := Finset.erase_subset_erase _ hsub
    have hκ' : ∀ e ∈ F'.erase s(ℓ, u), κ e = U := fun e he' ↦ hκ e (mem_of_mem_erase he')
    have hfor' : IsForest (F'.erase s(ℓ, u)) := hfor.subset (erase_subset _ _)
    have hnd' : ∀ e ∈ F'.erase s(ℓ, u), ¬ e.IsDiag := fun e he' ↦ hnd e (mem_of_mem_erase he')
    have hsep' : ∀ r₁ ∈ R, ∀ r₂ ∈ R, (graphOf (F'.erase s(ℓ, u))).Reachable r₁ r₂ → r₁ = r₂ :=
      fun r₁ h₁ r₂ h₂ h ↦ hsep r₁ h₁ r₂ h₂ (reachable_mono (erase_subset _ _) h)
    have hdiff : S.erase s(ℓ, u) \ F'.erase s(ℓ, u) = S \ F' := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, heS'⟩, hn⟩
        exact ⟨heS', fun heF ↦ hn ⟨hne, heF⟩⟩
      · rintro ⟨heS', heF⟩
        exact ⟨⟨fun h ↦ heF (h ▸ he), heS'⟩, fun h ↦ heF h.2⟩
    have hout' : ∀ e ∈ S.erase s(ℓ, u) \ F'.erase s(ℓ, u), ∀ v ∈ e, v ∈ R := by
      rw [hdiff]; exact hout
    -- the integrated leaf is bounded by `b_ℓ Δ`
    have happ0 : ∀ y, 0 ≤ (BddFun.apply U (φ ℓ)) y := fun y ↦
      integral_nonneg fun z ↦ mul_nonneg (U.nonneg _ _) (hφ0 ℓ z)
    have happ : ∀ y, (BddFun.apply U (φ ℓ)) y ≤ b ℓ * Δ := by
      intro y
      have h1 : (BddFun.apply U (φ ℓ)) y ≤ ∫ z, U y z * b ℓ ∂μ :=
        integral_mono (integrable_kernel_mul U (φ ℓ) y)
          (integrable_kernel_mul U (BddFun.const (b ℓ)) y)
          fun z ↦ mul_le_mul_of_nonneg_left (hb ℓ hℓR z) (U.nonneg _ _)
      rw [integral_mul_const] at h1
      calc (BddFun.apply U (φ ℓ)) y ≤ degree U y * b ℓ := h1
        _ ≤ Δ * b ℓ := mul_le_mul_of_nonneg_right (hdeg y) (hb0 ℓ)
        _ = b ℓ * Δ := mul_comm _ _
    have hℓ_in : ℓ ∈ univ \ R := by simp [hℓR]
    by_cases huR : u ∈ R
    · -- the leaf hangs off `R`: absorb the factor `b_ℓ Δ` directly
      set φ'' := Function.update φ ℓ BddFun.one with hφ''
      have hstep : wInt κ (S.erase s(ℓ, u)) (Function.update (Function.update φ ℓ BddFun.one) u
          ((φ u).mul (BddFun.apply U (φ ℓ)))) ≤ (b ℓ * Δ) * wInt κ (S.erase s(ℓ, u)) φ'' := by
        unfold wInt
        rw [← integral_const_mul]
        refine integral_mono (integrable_integrand _ _ _)
          ((integrable_integrand _ _ _).const_mul _) fun x ↦ ?_
        simp only []
        unfold vertexProd
        rw [prod_univ_eq_mul_erase _ u, prod_univ_eq_mul_erase (fun v ↦ φ'' v (x v)) u]
        rw [Function.update_self]
        have hrest : ∏ v ∈ univ.erase u, (Function.update (Function.update φ ℓ BddFun.one) u
            ((φ u).mul (BddFun.apply U (φ ℓ)))) v (x v) =
            ∏ v ∈ univ.erase u, φ'' v (x v) :=
          Finset.prod_congr rfl fun v hv ↦ by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
        rw [hrest]
        have hφ''u : φ'' u (x u) = φ u (x u) := by
          rw [hφ'', Function.update_of_ne hℓu.symm]
        rw [hφ''u, BddFun.mul_apply]
        have hrest0 : 0 ≤ ∏ v ∈ univ.erase u, φ'' v (x v) :=
          Finset.prod_nonneg fun v _ ↦ by
            rw [hφ'']
            by_cases hvℓ : v = ℓ
            · subst hvℓ; simp [BddFun.one]
            · rw [Function.update_of_ne hvℓ]; exact hφ0 v _
        have hE := edgeProd_nonneg κ (S.erase s(ℓ, u)) x
        have hφu := hφ0 u (x u)
        have := mul_le_mul_of_nonneg_left (happ (x u)) (mul_nonneg hφu (mul_nonneg hE hrest0))
        nlinarith [this]
      refine hstep.trans ?_
      have hφ''0 : ∀ v y, 0 ≤ φ'' v y := by
        intro v y
        rw [hφ'']
        by_cases hvℓ : v = ℓ
        · subst hvℓ; simp [BddFun.one]
        · rw [Function.update_of_ne hvℓ]; exact hφ0 v y
      set b'' := Function.update b ℓ 1 with hb''def
      have hb''0 : ∀ v, 0 ≤ b'' v := by
        intro v; rw [hb''def]
        by_cases hvℓ : v = ℓ
        · subst hvℓ; simp
        · rw [Function.update_of_ne hvℓ]; exact hb0 v
      have hb''le : ∀ v, v ∉ R → ∀ y, φ'' v y ≤ b'' v := by
        intro v hv y
        rw [hφ'', hb''def]
        by_cases hvℓ : v = ℓ
        · subst hvℓ; simp [BddFun.one]
        · rw [Function.update_of_ne hvℓ, Function.update_of_ne hvℓ]; exact hb v hv y
      have hih := ih (S.erase s(ℓ, u)) (F'.erase s(ℓ, u)) hcard hsub' hκ' hfor' hnd' hsep'
        hout' φ'' b'' hφ''0 hb''0 hb''le
      rw [hdiff, hcard] at hih
      have hres : wInt κ (S \ F') (fun v ↦ if v ∈ R then φ'' v else BddFun.one) =
          wInt κ (S \ F') (fun v ↦ if v ∈ R then φ v else BddFun.one) := by
        apply wInt_congr_weight
        intro v y
        by_cases hv : v ∈ R
        · have hvℓ : v ≠ ℓ := fun h ↦ hℓR (h ▸ hv)
          simp [hv, hφ'', Function.update_of_ne hvℓ]
        · simp [hv]
      rw [hres] at hih
      have hprod : b ℓ * ∏ v ∈ univ \ R, b'' v = ∏ v ∈ univ \ R, b v := by
        rw [hb''def, Finset.prod_update_of_mem hℓ_in, one_mul,
          ← Finset.mul_prod_erase (univ \ R) b hℓ_in, Finset.sdiff_singleton_eq_erase]
      rw [Finset.card_erase_of_mem he, hF'] at *
      have hW0 := wInt_nonneg κ (S \ F') (φ := fun v ↦ if v ∈ R then φ v else BddFun.one)
        (fun v y ↦ by by_cases hv : v ∈ R <;> simp [hv, hφ0, BddFun.one])
      have hbℓ := hb0 ℓ
      calc b ℓ * Δ * wInt κ (S.erase s(ℓ, u)) φ''
          ≤ b ℓ * Δ * (Δ ^ n * (∏ v ∈ univ \ R, b'' v) *
              wInt κ (S \ F') (fun v ↦ if v ∈ R then φ v else BddFun.one)) :=
            mul_le_mul_of_nonneg_left hih (mul_nonneg hbℓ hΔ0)
        _ = Δ ^ (n + 1) * (b ℓ * ∏ v ∈ univ \ R, b'' v) *
              wInt κ (S \ F') (fun v ↦ if v ∈ R then φ v else BddFun.one) := by ring
        _ = Δ ^ (n + 1) * (∏ v ∈ univ \ R, b v) *
              wInt κ (S \ F') (fun v ↦ if v ∈ R then φ v else BddFun.one) := by rw [hprod]
    · -- the leaf hangs off another free vertex: move the factor into its bound
      set φ' := Function.update (Function.update φ ℓ BddFun.one) u
        ((φ u).mul (BddFun.apply U (φ ℓ))) with hφ'
      set b' := Function.update (Function.update b ℓ 1) u (b u * (b ℓ * Δ)) with hb'
      have hφ'0 : ∀ v y, 0 ≤ φ' v y := by
        intro v y
        rw [hφ']
        by_cases hvu : v = u
        · subst hvu; rw [Function.update_self]
          exact mul_nonneg (hφ0 v y) (happ0 y)
        · rw [Function.update_of_ne hvu]
          by_cases hvℓ : v = ℓ
          · subst hvℓ; simp [BddFun.one]
          · rw [Function.update_of_ne hvℓ]; exact hφ0 v y
      have hb'0 : ∀ v, 0 ≤ b' v := by
        intro v; rw [hb']
        by_cases hvu : v = u
        · subst hvu; rw [Function.update_self]
          exact mul_nonneg (hb0 v) (mul_nonneg (hb0 ℓ) hΔ0)
        · rw [Function.update_of_ne hvu]
          by_cases hvℓ : v = ℓ
          · subst hvℓ; simp
          · rw [Function.update_of_ne hvℓ]; exact hb0 v
      have hb'' : ∀ v, v ∉ R → ∀ y, φ' v y ≤ b' v := by
        intro v hv y
        rw [hφ', hb']
        by_cases hvu : v = u
        · subst hvu; rw [Function.update_self, Function.update_self, BddFun.mul_apply]
          exact mul_le_mul (hb v hv y) (happ y) (happ0 y) (hb0 v)
        · rw [Function.update_of_ne hvu, Function.update_of_ne hvu]
          by_cases hvℓ : v = ℓ
          · subst hvℓ; simp [BddFun.one]
          · rw [Function.update_of_ne hvℓ, Function.update_of_ne hvℓ]; exact hb v hv y
      have hih := ih (S.erase s(ℓ, u)) (F'.erase s(ℓ, u)) hcard hsub' hκ' hfor' hnd' hsep'
        hout' φ' b' hφ'0 hb'0 hb''
      rw [hdiff] at hih
      have hres : wInt κ (S \ F') (fun v ↦ if v ∈ R then φ' v else BddFun.one) =
          wInt κ (S \ F') (fun v ↦ if v ∈ R then φ v else BddFun.one) := by
        apply wInt_congr_weight
        intro v y
        by_cases hv : v ∈ R
        · have hvℓ : v ≠ ℓ := fun h ↦ hℓR (h ▸ hv)
          have hvu : v ≠ u := fun h ↦ huR (h ▸ hv)
          simp [hv, hφ', Function.update_of_ne hvℓ, Function.update_of_ne hvu]
        · simp [hv]
      rw [hres] at hih
      have hu_in : u ∈ univ \ R := by simp [huR]
      have hℓ_in' : ℓ ∈ (univ \ R) \ {u} := by simp [hℓR, hℓu]
      have hprod : ∏ v ∈ univ \ R, b' v = Δ * ∏ v ∈ univ \ R, b v := by
        rw [hb', Finset.prod_update_of_mem hu_in, Finset.prod_update_of_mem hℓ_in', one_mul,
          ← Finset.mul_prod_erase (univ \ R) b hu_in]
        have h1 : (univ \ R).erase u = (univ \ R) \ {u} :=
          (Finset.sdiff_singleton_eq_erase u _).symm
        rw [h1, ← Finset.mul_prod_erase ((univ \ R) \ {u}) b hℓ_in']
        have h2 : ((univ \ R) \ {u}).erase ℓ = ((univ \ R) \ {u}) \ {ℓ} :=
          (Finset.sdiff_singleton_eq_erase ℓ _).symm
        rw [h2]; ring
      rw [hprod, hcard] at hih
      rw [hF']
      calc wInt κ (S.erase s(ℓ, u)) φ'
          ≤ Δ ^ n * (Δ * ∏ v ∈ univ \ R, b v) *
              wInt κ (S \ F') (fun v ↦ if v ∈ R then φ v else BddFun.one) := hih
        _ = Δ ^ (n + 1) * (∏ v ∈ univ \ R, b v) *
              wInt κ (S \ F') (fun v ↦ if v ∈ R then φ v else BddFun.one) := by ring

end Taeyoung.Paper.Eventual
