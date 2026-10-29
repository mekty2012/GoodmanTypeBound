import Taeyoung.Paper.Eventual.LocalPrelim

/-!
# The quantity `D_H` and the remainder `R_H` (`paper.pdf`, Section 4.6:
Lemmas 4.13 and 4.14)

For a graphon `K` write `q = ∫ K` and

* `D_H(K) = t(H, 1-K) - 1 + m q`, the integral of
  `φ(a) = ∏_e (1 - a_e) - 1 + ∑_e a_e ≥ 0` (`Dfun`, `Dfun_nonneg`; Lemma 4.13);
* `R_H(q) = Ψ_H(q) - 1 + mq = ∑_{B(F)=∅, |F| ≥ 2} (-q)^{|F|}` (`remPoly`).

Proved here:

* `Dfun_superadd`: `D_H(K₁) + D_H(K₂) ≤ D_H(K₁+K₂)` (4.31),
  from `∏(1-a) + ∏(1-b) ≤ ∏(1-a-b) + 1`;
* `gammaFun_eq`: `Γ_H(K) = D_H(K) - R_H(q)`;
* `abs_remPoly_sub_le`: **Lemma 4.14**,
  `|R_H(q) - R_H(q₂)| ≤ 2 m² q (q - q₂)` for `0 ≤ q₂ ≤ q`, `mq ≤ 1/2`.
-/

open MeasureTheory Finset SimpleGraph Polynomial

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-! ### Pointwise inequalities -/

lemma one_sub_sum_le_prod (E : Finset (Sym2 V)) (a : Sym2 V → ℝ) (h0 : ∀ e ∈ E, 0 ≤ a e)
    (h1 : ∀ e ∈ E, a e ≤ 1) : 1 - ∑ e ∈ E, a e ≤ ∏ e ∈ E, (1 - a e) := by
  induction E using Finset.induction_on with
  | empty => simp
  | @insert f E hf ih =>
    rw [Finset.sum_insert hf, Finset.prod_insert hf]
    have ih' := ih (fun e he ↦ h0 e (mem_insert_of_mem he)) (fun e he ↦ h1 e (mem_insert_of_mem he))
    have hf0 := h0 f (mem_insert_self f E)
    have hf1 := h1 f (mem_insert_self f E)
    have hP : 0 ≤ ∏ e ∈ E, (1 - a e) :=
      Finset.prod_nonneg fun e he ↦ by linarith [h1 e (mem_insert_of_mem he)]
    have hS : 0 ≤ ∑ e ∈ E, a e := Finset.sum_nonneg fun e he ↦ h0 e (mem_insert_of_mem he)
    nlinarith

lemma prod_add_prod_le (E : Finset (Sym2 V)) (a b : Sym2 V → ℝ) (ha : ∀ e ∈ E, 0 ≤ a e)
    (hb : ∀ e ∈ E, 0 ≤ b e) (hab : ∀ e ∈ E, a e + b e ≤ 1) :
    (∏ e ∈ E, (1 - a e)) + ∏ e ∈ E, (1 - b e) ≤ (∏ e ∈ E, (1 - (a e + b e))) + 1 := by
  induction E using Finset.induction_on with
  | empty => norm_num
  | @insert f E hf ih =>
    rw [Finset.prod_insert hf, Finset.prod_insert hf, Finset.prod_insert hf]
    have ih' := ih (fun e he ↦ ha e (mem_insert_of_mem he)) (fun e he ↦ hb e (mem_insert_of_mem he))
      (fun e he ↦ hab e (mem_insert_of_mem he))
    have ha0 := ha f (mem_insert_self f E)
    have hb0 := hb f (mem_insert_self f E)
    have hab1 := hab f (mem_insert_self f E)
    set A := ∏ e ∈ E, (1 - a e)
    set B := ∏ e ∈ E, (1 - b e)
    set P := ∏ e ∈ E, (1 - (a e + b e))
    have hA1 : A ≤ 1 := Finset.prod_le_one (fun e he ↦ by
        linarith [hab e (mem_insert_of_mem he), hb e (mem_insert_of_mem he)])
      fun e he ↦ by linarith [ha e (mem_insert_of_mem he)]
    have hB1 : B ≤ 1 := Finset.prod_le_one (fun e he ↦ by
        linarith [hab e (mem_insert_of_mem he), ha e (mem_insert_of_mem he)])
      fun e he ↦ by linarith [hb e (mem_insert_of_mem he)]
    have hstep : (A + B - 1) * (1 - (a f + b f)) ≤ P * (1 - (a f + b f)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith

/-! ### `D_H` -/

/-- `φ(a) = ∏ (1 - a_e) - 1 + ∑ a_e`, evaluated on the graphon values. -/
noncomputable def Dint (H : SimpleGraph V) [DecidableRel H.Adj] (K : Graphon Ω μ)
    (x : V → Ω) : ℝ :=
  ∏ e ∈ H.edgeFinset, (1 - edgeValue K x e) - 1 + ∑ e ∈ H.edgeFinset, edgeValue K x e

/-- `D_H(K) = t(H,1-K) - 1 + m ∫ K`. -/
noncomputable def Dfun (H : SimpleGraph V) [DecidableRel H.Adj] (K : Graphon Ω μ) : ℝ :=
  homDensity H K.compl - 1 + H.edgeFinset.card * meanDeg K

lemma Dint_nonneg (K : Graphon Ω μ) (x : V → Ω) : 0 ≤ Dint H K x := by
  unfold Dint
  have := one_sub_sum_le_prod H.edgeFinset (fun e ↦ edgeValue K x e)
    (fun e _ ↦ edgeValue_nonneg K x e) (fun e _ ↦ edgeValue_le_one K x e)
  linarith

lemma measurable_Dint (K : Graphon Ω μ) : Measurable (Dint (V := V) H K) := by
  unfold Dint
  exact ((Finset.measurable_fun_prod _ fun e _ ↦ measurable_const.sub
    (measurable_edgeValue K e)).sub measurable_const).add
    (Finset.measurable_fun_sum _ fun e _ ↦ measurable_edgeValue K e)

lemma abs_Dint_le (K : Graphon Ω μ) (x : V → Ω) :
    |Dint H K x| ≤ 2 + H.edgeFinset.card := by
  unfold Dint
  have h1 : |∏ e ∈ H.edgeFinset, (1 - edgeValue K x e)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun e _ ↦ abs_nonneg _) fun e _ ↦ by
      rw [abs_le]; constructor <;> linarith [edgeValue_nonneg K x e, edgeValue_le_one K x e]
  have h2 : |∑ e ∈ H.edgeFinset, edgeValue K x e| ≤ H.edgeFinset.card := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun e _ ↦ edgeValue_nonneg K x e)]
    calc ∑ e ∈ H.edgeFinset, edgeValue K x e ≤ ∑ _e ∈ H.edgeFinset, (1 : ℝ) :=
          Finset.sum_le_sum fun e _ ↦ edgeValue_le_one K x e
      _ = H.edgeFinset.card := by simp
  calc |∏ e ∈ H.edgeFinset, (1 - edgeValue K x e) - 1 + ∑ e ∈ H.edgeFinset, edgeValue K x e|
      ≤ |∏ e ∈ H.edgeFinset, (1 - edgeValue K x e)| + |(1 : ℝ)| +
          |∑ e ∈ H.edgeFinset, edgeValue K x e| := by
        refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
        exact abs_sub _ _
    _ ≤ 2 + H.edgeFinset.card := by norm_num; linarith

lemma integrable_Dint (K : Graphon Ω μ) :
    Integrable (Dint (V := V) H K) (assignmentMeasure V μ) :=
  integrable_of_bounded (measurable_Dint K) (abs_Dint_le K)

/-- The density of a single edge is `∫ K`. -/
lemma integral_edgeValue (K : Graphon Ω μ) {e : Sym2 V} (hnd : ¬ e.IsDiag) :
    ∫ x, edgeValue K x e ∂assignmentMeasure V μ = meanDeg K := by
  induction e using Sym2.inductionOn with
  | _ u w =>
  have huw : u ≠ w := fun h ↦ hnd (by simp [h])
  set φ : Fin 2 → V := ![u, w]
  have hφ : Function.Injective φ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [φ, huw.symm]
  have hg : Measurable fun y : Fin 2 → Ω ↦ K (y 0) (y 1) :=
    K.measurable.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1) :
      Measurable fun y : Fin 2 → Ω ↦ (y 0, y 1))
  have h1 : ∫ x, edgeValue K x s(u, w) ∂assignmentMeasure V μ =
      ∫ x, (fun y : Fin 2 → Ω ↦ K (y 0) (y 1)) (x ∘ φ) ∂assignmentMeasure V μ := by
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp [φ]
  rw [h1, integral_comp_injective hφ hg]
  have h2 : ∫ y, K (y 0) (y 1) ∂assignmentMeasure (Fin 2) μ = cliqueDensity 2 K := by
    unfold cliqueDensity homDensity
    exact integral_congr_ae (ae_of_all _ fun y ↦ (graphWeight_top_fin_two K y).symm)
  rw [h2, ← integral_degree]
  rfl

/-- `D_H(K) = ∫ φ(K)`. -/
theorem Dfun_eq (K : Graphon Ω μ) :
    Dfun H K = ∫ x, Dint H K x ∂assignmentMeasure V μ := by
  have hnd := not_isDiag_of_mem_edgeFinset H
  unfold Dint
  have hprod : Integrable (fun x : V → Ω ↦ ∏ e ∈ H.edgeFinset, (1 - edgeValue K x e))
      (assignmentMeasure V μ) := by
    refine integrable_of_bounded (Finset.measurable_fun_prod _ fun e _ ↦ measurable_const.sub
      (measurable_edgeValue K e)) (C := 1) fun x ↦ ?_
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun e _ ↦ abs_nonneg _) fun e _ ↦ by
      rw [abs_le]; constructor <;> linarith [edgeValue_nonneg K x e, edgeValue_le_one K x e]
  have hsum : ∀ e, Integrable (fun x : V → Ω ↦ edgeValue K x e) (assignmentMeasure V μ) :=
    fun e ↦ integrable_of_bounded (measurable_edgeValue K e) (C := 1) fun x ↦ by
      rw [abs_of_nonneg (edgeValue_nonneg K x e)]; exact edgeValue_le_one K x e
  have hA : Integrable (fun x : V → Ω ↦ ∏ e ∈ H.edgeFinset, (1 - edgeValue K x e) - 1)
      (assignmentMeasure V μ) := hprod.sub (integrable_const 1)
  have hB : Integrable (fun x : V → Ω ↦ ∑ e ∈ H.edgeFinset, edgeValue K x e)
      (assignmentMeasure V μ) := integrable_finsetSum _ fun e _ ↦ hsum e
  rw [integral_add hA hB, integral_sub hprod (integrable_const 1),
    integral_finsetSum _ fun e _ ↦ hsum e]
  have h1 : ∫ x, ∏ e ∈ H.edgeFinset, (1 - edgeValue K x e) ∂assignmentMeasure V μ =
      homDensity H K.compl := by
    unfold homDensity graphWeight
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [edgeValue_compl]
  rw [h1, Finset.sum_congr rfl fun e he ↦ integral_edgeValue K (hnd e he)]
  simp [Dfun]

lemma Dfun_nonneg (K : Graphon Ω μ) : 0 ≤ Dfun H K := by
  rw [Dfun_eq]; exact integral_nonneg fun x ↦ Dint_nonneg K x

/-- **(4.31)** (Lemma 4.13). -/
theorem Dfun_superadd (K₁ K₂ K : Graphon Ω μ) (h : ∀ x y, K x y = K₁ x y + K₂ x y) :
    Dfun H K₁ + Dfun H K₂ ≤ Dfun H K := by
  rw [Dfun_eq, Dfun_eq, Dfun_eq, ← integral_add (integrable_Dint K₁) (integrable_Dint K₂)]
  refine integral_mono ((integrable_Dint K₁).add (integrable_Dint K₂)) (integrable_Dint K)
    fun x ↦ ?_
  have hval : ∀ e, edgeValue K x e = edgeValue K₁ x e + edgeValue K₂ x e := by
    intro e; induction e using Sym2.inductionOn with
    | _ u w => simp [h]
  have := prod_add_prod_le H.edgeFinset (fun e ↦ edgeValue K₁ x e) (fun e ↦ edgeValue K₂ x e)
    (fun e _ ↦ edgeValue_nonneg _ x e) (fun e _ ↦ edgeValue_nonneg _ x e)
    (fun e _ ↦ by rw [← hval]; exact edgeValue_le_one K x e)
  show Dint H K₁ x + Dint H K₂ x ≤ Dint H K x
  unfold Dint
  simp_rw [hval, Finset.sum_add_distrib]
  linarith

/-! ### `R_H` -/

open scoped Classical in
/-- `R_H(q) = ∑_{B(F) = ∅, |F| ≥ 2} (-q)^{|F|}`. -/
noncomputable def remPoly (E : Finset (Sym2 V)) (q : ℝ) : ℝ :=
  ∑ F ∈ (openForests E).filter (fun F ↦ 2 ≤ F.card), (-q) ^ F.card

/-- Edge sets with at most one edge are open forests. -/
lemma mem_openForests_of_card_le_one (hcyc : ¬ H.IsAcyclic) {F : Finset (Sym2 V)}
    (hFE : F ⊆ H.edgeFinset) (hF : F.card ≤ 1) : F ∈ openForests H.edgeFinset := by
  refine mem_openForests.mpr ⟨mem_forests.mpr ⟨hFE, isForest_of_card_le_two (by omega)⟩, ?_⟩
  by_contra hB
  have := girth_le_card_add_one hFE hB
  have := H.three_le_girth hcyc
  omega

/-- **The remainder `R_H`**: `Ψ_H(q) = Φ_H(1-q) = 1 - mq + R_H(q)`. -/
theorem chromaticTarget_eq_rem (hcyc : ¬ H.IsAcyclic) {P : ℝ[X]}
    (hP : IsChromaticPolynomial H P) (q : ℝ) :
    chromaticTarget (V := V) P (1 - q) = 1 - H.edgeFinset.card * q + remPoly H.edgeFinset q := by
  classical
  rw [chromaticTarget_eq_forest_sum H hP, remPoly,
    ← Finset.sum_filter_add_sum_filter_not (openForests H.edgeFinset) (fun F ↦ 2 ≤ F.card)]
  have hsmall : (openForests H.edgeFinset).filter (fun F ↦ ¬ 2 ≤ F.card) =
      H.edgeFinset.powerset.filter (fun F ↦ F.card ≤ 1) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_powerset, not_le]
    constructor
    · rintro ⟨hF, hc⟩
      exact ⟨(mem_forests.mp (mem_openForests.mp hF).1).1, by omega⟩
    · rintro ⟨hFE, hc⟩
      exact ⟨mem_openForests_of_card_le_one hcyc hFE hc, by omega⟩
  have hS : ∑ F ∈ H.edgeFinset.powerset.filter (fun F ↦ F.card ≤ 1), (-q) ^ F.card =
      1 - H.edgeFinset.card * q := by
    rw [Finset.sum_filter]
    rw [Finset.sum_powerset_apply_card (fun r ↦ if r ≤ 1 then (-q) ^ r else 0)]
    have hm : 1 ≤ H.edgeFinset.card := by
      obtain ⟨F, hF, hc, -⟩ := exists_adjacent_open hcyc
      have := Finset.card_le_card (mem_forests.mp (mem_openForests.mp hF).1).1
      omega
    obtain ⟨k, hk⟩ : ∃ k, H.edgeFinset.card = k + 1 := ⟨_, (Nat.sub_add_cancel hm).symm⟩
    rw [hk, Finset.sum_range_succ', Finset.sum_range_succ']
    have hrest : ∑ i ∈ Finset.range k, (k + 1).choose (i + 1 + 1) •
        (if i + 1 + 1 ≤ 1 then (-q) ^ (i + 1 + 1) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ ↦ by simp
    rw [hrest]
    simp
    ring
  rw [hsmall, hS]
  ring

/-- `Γ_H(K) = t(H,1-K) - Φ_H(1 - ∫K)`. -/
noncomputable def gammaFun (H : SimpleGraph V) [DecidableRel H.Adj] (P : ℝ[X])
    (K : Graphon Ω μ) : ℝ :=
  homDensity H K.compl - chromaticTarget (V := V) P (1 - meanDeg K)

/-- `Γ_H(K) = D_H(K) - R_H(∫ K)`. -/
lemma gammaFun_eq (hcyc : ¬ H.IsAcyclic) {P : ℝ[X]} (hP : IsChromaticPolynomial H P)
    (K : Graphon Ω μ) : gammaFun H P K = Dfun H K - remPoly H.edgeFinset (meanDeg K) := by
  unfold gammaFun Dfun
  rw [chromaticTarget_eq_rem hcyc hP]
  ring

lemma edgeDensity_compl (K : Graphon Ω μ) : edgeDensity K.compl = 1 - meanDeg K := by
  rw [edgeDensity, ← integral_degree]
  simp_rw [degree_compl]
  rw [integral_sub (integrable_const _) (isBdd_degree K).integrable]
  simp [meanDeg]

/-! ### Lemma 4.14 -/

lemma pow_sub_pow_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    ∀ r : ℕ, a ^ (r + 1) - b ^ (r + 1) ≤ (r + 1) * a ^ r * (a - b)
  | 0 => by simp
  | r + 1 => by
    have ih := pow_sub_pow_le hb hab r
    have ha : 0 ≤ a := hb.trans hab
    have h1 : b ^ (r + 1) ≤ a ^ (r + 1) := pow_le_pow_left₀ hb hab _
    have hsplit : a ^ (r + 1 + 1) - b ^ (r + 1 + 1) =
        a * (a ^ (r + 1) - b ^ (r + 1)) + b ^ (r + 1) * (a - b) := by ring
    rw [hsplit]
    have e1 : a * (a ^ (r + 1) - b ^ (r + 1)) ≤ a * ((r + 1) * a ^ r * (a - b)) :=
      mul_le_mul_of_nonneg_left ih ha
    have e2 : b ^ (r + 1) * (a - b) ≤ a ^ (r + 1) * (a - b) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    push_cast
    have : a * ((↑r + 1) * a ^ r * (a - b)) = (↑r + 1) * a ^ (r + 1) * (a - b) := by ring
    nlinarith

lemma abs_neg_pow_sub_le {q q₂ : ℝ} (hq₂ : 0 ≤ q₂) (hq : q₂ ≤ q) {r : ℕ} (hr : 1 ≤ r) :
    |(-q) ^ r - (-q₂) ^ r| ≤ r * q ^ (r - 1) * (q - q₂) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [neg_pow, neg_pow (q₂), ← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hq₂ hq _))]
  have := pow_sub_pow_le hq₂ hq k
  simpa using this

lemma choose_mul_le_pow (m r : ℕ) : m.choose r * r ≤ m ^ r := by
  have h1 : m.choose r * r.factorial ≤ m ^ r := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow m r
  have h2 : r ≤ r.factorial := Nat.self_le_factorial r
  calc m.choose r * r ≤ m.choose r * r.factorial := Nat.mul_le_mul_left _ h2
    _ ≤ m ^ r := h1

/-- `∑_{F ⊆ E, |F| ≥ 2} |F| q^{|F|-1} ≤ 2 m² q` for `0 ≤ mq ≤ 1/2`. -/
lemma sum_card_pow_le (E : Finset (Sym2 V)) {q : ℝ} (hq0 : 0 ≤ q)
    (hmq : (E.card : ℝ) * q ≤ 1 / 2) :
    ∑ F ∈ E.powerset, (if 2 ≤ F.card then (F.card : ℝ) * q ^ (F.card - 1) else 0) ≤
      2 * (E.card : ℝ) ^ 2 * q := by
  set m := E.card
  rw [Finset.sum_powerset_apply_card (fun r ↦ if 2 ≤ r then (r : ℝ) * q ^ (r - 1) else 0)]
  have hterm : ∀ r ∈ Finset.range (m + 1), (m.choose r) • (if 2 ≤ r then (r : ℝ) * q ^ (r - 1)
      else 0) ≤ if 2 ≤ r then (m : ℝ) * ((m : ℝ) * q) ^ (r - 1) else 0 := by
    intro r _
    split_ifs with h2
    · rw [nsmul_eq_mul]
      have hc : ((m.choose r * r : ℕ) : ℝ) ≤ (m : ℝ) ^ r := by exact_mod_cast choose_mul_le_pow m r
      push_cast at hc
      have hmr : (m : ℝ) ^ r = (m : ℝ) * (m : ℝ) ^ (r - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hq' := pow_nonneg hq0 (r - 1)
      rw [mul_pow]
      calc (m.choose r : ℝ) * ((r : ℝ) * q ^ (r - 1)) = ((m.choose r : ℝ) * r) * q ^ (r - 1) := by
            ring
        _ ≤ (m : ℝ) ^ r * q ^ (r - 1) := mul_le_mul_of_nonneg_right hc hq'
        _ = (m : ℝ) * ((m : ℝ) ^ (r - 1) * q ^ (r - 1)) := by rw [hmr]; ring
    · simp
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsplit : ∑ r ∈ Finset.range (m + 1), (if 2 ≤ r then (m : ℝ) * ((m : ℝ) * q) ^ (r - 1)
      else 0) = ∑ j ∈ Finset.range (m + 1 - 2), (m : ℝ) * ((m : ℝ) * q) ^ (j + 1) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (min 2 (m + 1)))
      (min_le_right 2 (m + 1))]
    have h1 : ∑ r ∈ Finset.Ico 0 (min 2 (m + 1)), (if 2 ≤ r then (m : ℝ) *
        ((m : ℝ) * q) ^ (r - 1) else 0) = 0 :=
      Finset.sum_eq_zero fun r hr ↦ by
        rw [if_neg]; have := (Finset.mem_Ico.mp hr).2; omega
    rw [h1, zero_add, Finset.sum_Ico_eq_sum_range]
    by_cases hm : 2 ≤ m + 1
    · rw [min_eq_left hm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [if_pos (by omega)]; congr 2; omega
    · have : m + 1 - min 2 (m + 1) = 0 := by omega
      rw [this, show m + 1 - 2 = 0 by omega]
      simp only [Finset.sum_range_zero]
  rw [hsplit, ← Finset.mul_sum]
  have hg := geom_le (mul_nonneg (Nat.cast_nonneg m) hq0) hmq (m + 1 - 2)
  calc (m : ℝ) * ∑ j ∈ Finset.range (m + 1 - 2), ((m : ℝ) * q) ^ (j + 1)
      ≤ (m : ℝ) * (2 * ((m : ℝ) * q)) := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg m)
    _ = 2 * (m : ℝ) ^ 2 * q := by ring

/-- **Lemma 4.14**. -/
theorem abs_remPoly_sub_le (E : Finset (Sym2 V)) {q q₂ : ℝ} (hq₂ : 0 ≤ q₂) (hq : q₂ ≤ q)
    (hmq : (E.card : ℝ) * q ≤ 1 / 2) :
    |remPoly E q - remPoly E q₂| ≤ 2 * (E.card : ℝ) ^ 2 * q * (q - q₂) := by
  classical
  unfold remPoly
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hq0 : 0 ≤ q := hq₂.trans hq
  calc ∑ F ∈ (openForests E).filter (fun F ↦ 2 ≤ F.card), |(-q) ^ F.card - (-q₂) ^ F.card|
      ≤ ∑ F ∈ (openForests E).filter (fun F ↦ 2 ≤ F.card),
          (F.card : ℝ) * q ^ (F.card - 1) * (q - q₂) :=
        Finset.sum_le_sum fun F hF ↦ abs_neg_pow_sub_le hq₂ hq
          (by have := (Finset.mem_filter.mp hF).2; omega)
    _ ≤ ∑ F ∈ E.powerset, (if 2 ≤ F.card then (F.card : ℝ) * q ^ (F.card - 1) else 0) *
          (q - q₂) := by
        simp_rw [ite_mul, zero_mul]
        rw [← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun F hF ↦ ?_) (fun F _ _ ↦ ?_)
        · obtain ⟨hF, h2⟩ := Finset.mem_filter.mp hF
          exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
            (mem_forests.mp (mem_openForests.mp hF).1).1, h2⟩
        · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 _)) (by linarith)
    _ = (∑ F ∈ E.powerset, (if 2 ≤ F.card then (F.card : ℝ) * q ^ (F.card - 1) else 0)) *
          (q - q₂) := by rw [Finset.sum_mul]
    _ ≤ 2 * (E.card : ℝ) ^ 2 * q * (q - q₂) :=
        mul_le_mul_of_nonneg_right (sum_card_pow_le E hq0 (by
          calc (E.card : ℝ) * q ≤ (E.card : ℝ) * q := le_rfl
            _ ≤ 1 / 2 := hmq)) (by linarith)

end Taeyoung.Paper.Eventual
