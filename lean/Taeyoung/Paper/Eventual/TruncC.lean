import Taeyoung.Paper.Eventual.TruncB

/-!
# Quantitative truncation (`paper.pdf`, Proposition 4.15)

* `Dfun_high_ge`: `D_H(U₁) ≥ c_* t^{n-3} ∫_A g²`, from the events that exactly one
  vertex of `H` lies in `A` (the binomial bound (4.37));
* `Dfun_high_ge_mean` (in `TruncD.lean`): `D_H(U₁) ≥ (c_* δ/16) ∫ U₁` when `s ≤ δ/2`,
  `(n-3)s ≤ 1/2`;
* `truncation` (in `TruncD.lean`): **Proposition 4.15** for
  `δ = (6n⁶)⁻¹`: if every graphon of maximum degree at most `δ` satisfies the
  bound, then so does every graphon with `∫ U < δ²/2 = (72 n¹²)⁻¹`.
-/

open MeasureTheory Finset SimpleGraph Polynomial

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

lemma IsBdd.pow {f : Ω → ℝ} (hf : IsBdd f) : ∀ k : ℕ, IsBdd (fun x ↦ f x ^ k)
  | 0 => by simpa using IsBdd.const (Ω := Ω) 1
  | k + 1 => by simpa [pow_succ] using (IsBdd.pow hf k).mul hf

/-! ### The binomial bound -/

/-- `G_j = (t-g)^{j+1} - t^{j+1} + (j+1) t^j g` satisfies `G_0 = 0` and
`G_{j+1} = (t-g) G_j + (j+1) t^j g²`. -/
lemma binom_aux {t g : ℝ} (hg0 : 0 ≤ g) (hgt : g ≤ t) :
    ∀ j : ℕ, 0 ≤ (t - g) ^ (j + 1) - t ^ (j + 1) + (j + 1) * t ^ j * g ∧
      (j : ℝ) * t ^ (j - 1) * g ^ 2 ≤ (t - g) ^ (j + 1) - t ^ (j + 1) + (j + 1) * t ^ j * g
  | 0 => by simp
  | j + 1 => by
    obtain ⟨h0, -⟩ := binom_aux hg0 hgt j
    have hrec : (t - g) ^ (j + 1 + 1) - t ^ (j + 1 + 1) + ((j + 1 : ℕ) + 1 : ℝ) * t ^ (j + 1) * g =
        (t - g) * ((t - g) ^ (j + 1) - t ^ (j + 1) + (j + 1) * t ^ j * g) +
          (j + 1) * t ^ j * g ^ 2 := by push_cast; ring
    have ht : 0 ≤ t := hg0.trans hgt
    have hp := mul_nonneg (sub_nonneg.mpr hgt) h0
    have hq : 0 ≤ (j + 1 : ℝ) * t ^ j * g ^ 2 := by positivity
    push_cast at hrec ⊢
    rw [hrec]
    try simp only [Nat.add_sub_cancel]
    constructor <;> linarith

/-- **(4.37)**, homogeneous form:
`t^{N-k} (t-g)^k - t^N + k t^{N-1} g ≥ (k-1)_+ t^{N-2} g²`. -/
lemma binom_ge {t g : ℝ} (hg0 : 0 ≤ g) (hgt : g ≤ t) {k N : ℕ} (hkN : k ≤ N) :
    ((k - 1 : ℕ) : ℝ) * t ^ (N - 2) * g ^ 2 ≤
      t ^ (N - k) * (t - g) ^ k - t ^ N + k * t ^ (N - 1) * g := by
  have ht : 0 ≤ t := hg0.trans hgt
  rcases k with _ | j
  · simp
  · have hN1 : t ^ N = t ^ (N - (j + 1)) * t ^ (j + 1) := by rw [← pow_add]; congr 1; omega
    have hN2 : t ^ (N - 1) = t ^ (N - (j + 1)) * t ^ j := by rw [← pow_add]; congr 1; omega
    rw [hN1, hN2]
    obtain ⟨h0, h1⟩ := binom_aux hg0 hgt j
    have hc : 0 ≤ t ^ (N - (j + 1)) := pow_nonneg ht _
    have hkey : t ^ (N - (j + 1)) * (t - g) ^ (j + 1) - t ^ (N - (j + 1)) * t ^ (j + 1) +
        ((j + 1 : ℕ) : ℝ) * (t ^ (N - (j + 1)) * t ^ j) * g =
        t ^ (N - (j + 1)) * ((t - g) ^ (j + 1) - t ^ (j + 1) + (j + 1) * t ^ j * g) := by
      push_cast; ring
    rw [hkey]
    simp only [Nat.add_sub_cancel]
    rcases j with _ | i
    · norm_num
    · have hN3 : t ^ (N - 2) = t ^ (N - (i + 1 + 1)) * t ^ (i + 1 - 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hN3]
      have := mul_le_mul_of_nonneg_left h1 hc
      push_cast at this ⊢
      linarith

lemma ne_of_mem_nbr {v w : V} (hw : w ∈ H.neighborFinset v) : w ≠ v :=
  ((H.mem_neighborFinset v w).mp hw).ne.symm

/-! ### The events -/

section Events

variable (U : Graphon Ω μ) (δ : ℝ)

lemma prod_indAc (S : Finset V) :
    ∏ u ∈ S, ∫ y, indAc U δ y ∂μ = tA U δ ^ S.card := by
  rw [Finset.prod_const]; rfl

lemma card_erase_sdiff (v : V) :
    ((univ.erase v) \ H.neighborFinset v).card = Fintype.card V - 1 - H.degree v := by
  rw [Finset.card_sdiff_of_subset (fun w hw ↦ Finset.mem_erase.mpr
      ⟨ne_of_mem_nbr hw, mem_univ w⟩),
    Finset.card_erase_of_mem (mem_univ v), Finset.card_univ, H.card_neighborFinset_eq_degree]

/-- The product term. -/
lemma wInt_star_compl (v : V) :
    wInt (fun _ ↦ U.compl) (starEdges v (H.neighborFinset v)) (evWeight U δ v) =
      (∫ y, indA U δ y * (tA U δ - gA U δ y) ^ H.degree v ∂μ) *
        tA U δ ^ (Fintype.card V - 1 - H.degree v) := by
  rw [wInt_star _ v _ (H.notMem_neighborFinset_self v)]
  have hw : ∀ w ∈ H.neighborFinset v, evWeight U δ v w = indAc U δ := fun w hw ↦
    evWeight_ne U δ (ne_of_mem_nbr hw)
  have hu : ∀ u ∈ (univ.erase v) \ H.neighborFinset v, evWeight U δ v u = indAc U δ :=
    fun u hu ↦ evWeight_ne U δ (Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hu).1)
  rw [Finset.prod_congr rfl fun u hu' ↦ by rw [hu u hu'], prod_indAc, card_erase_sdiff]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []
  rw [evWeight_self, Finset.prod_congr rfl fun w hw' ↦ by
    rw [hw w hw', kernelApply_compl_indAc], Finset.prod_const, H.card_neighborFinset_eq_degree]

/-- A linear term. -/
lemma wInt_single (v w : V) (hwv : w ≠ v) :
    wInt (fun _ ↦ U) {s(v, w)} (evWeight U δ v) =
      (∫ y, indA U δ y * gA U δ y ∂μ) * tA U δ ^ (Fintype.card V - 2) := by
  have hS : ({s(v, w)} : Finset (Sym2 V)) = starEdges v {w} := by simp [starEdges]
  rw [hS, wInt_star _ v _ (by simpa using hwv.symm)]
  have hu : ∀ u ∈ (univ.erase v) \ {w}, evWeight U δ v u = indAc U δ :=
    fun u hu ↦ evWeight_ne U δ (Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hu).1)
  rw [Finset.prod_congr rfl fun u hu' ↦ by rw [hu u hu'], prod_indAc]
  have hcard : ((univ.erase v) \ {w}).card = Fintype.card V - 2 := by
    rw [Finset.card_sdiff_of_subset (by simpa using hwv), Finset.card_erase_of_mem (mem_univ v),
      Finset.card_univ, Finset.card_singleton]
    omega
  rw [hcard]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [Finset.prod_singleton]
  rw [evWeight_self, evWeight_ne U δ hwv]
  rfl

/-- The constant term. -/
lemma wInt_none (v : V) :
    wInt (fun _ ↦ U) ∅ (evWeight U δ v) = sA U δ * tA U δ ^ (Fintype.card V - 1) := by
  rw [wInt_empty, ← Finset.mul_prod_erase univ _ (mem_univ v), evWeight_self]
  rw [Finset.prod_congr rfl fun u hu ↦ by rw [evWeight_ne U δ (Finset.ne_of_mem_erase hu)],
    prod_indAc, Finset.card_erase_of_mem (mem_univ v), Finset.card_univ]
  rfl

lemma integrable_vertexProd_mul (v : V) {f : (V → Ω) → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) :
    Integrable (fun x ↦ vertexProd (evWeight U δ v) x * f x) (assignmentMeasure V μ) := by
  refine integrable_of_bounded ((measurable_vertexProd _).mul hf) (C := C) fun x ↦ ?_
  rw [abs_mul]
  have h0 := vertexProd_evWeight_nonneg U δ v x
  have h1 : vertexProd (evWeight U δ v) x ≤ 1 :=
    Finset.prod_le_one (fun u _ ↦ evWeight_nonneg U δ v u _) fun u _ ↦ evWeight_le_one U δ v u _
  rw [abs_of_nonneg h0]
  calc vertexProd (evWeight U δ v) x * |f x| ≤ 1 * C :=
        mul_le_mul h1 (hC x) (abs_nonneg _) zero_le_one
    _ = C := one_mul C

/-- **One vertex in `A`**: `∫ 1_{E_v} ψ_v ≥ (d_H(v)-1)_+ t^{n-3} ∫_A g²`. -/
theorem integral_event_ge (v : V) :
    ((H.degree v - 1 : ℕ) : ℝ) * tA U δ ^ (Fintype.card V - 3) *
        ∫ y, indA U δ y * gA U δ y ^ 2 ∂μ ≤
      ∫ x, vertexProd (evWeight U δ v) x * psiV (H := H) U v x ∂assignmentMeasure V μ := by
  classical
  set N := H.neighborFinset v
  set k := H.degree v
  set n := Fintype.card V
  set t := tA U δ
  set s := sA U δ
  have hkn : k ≤ n - 1 := by have := H.degree_lt_card_verts v; omega
  -- split the integrand
  have hprod_meas : Measurable fun x : V → Ω ↦ ∏ e ∈ starEdges v N, (1 - edgeValue U x e) :=
    Finset.measurable_fun_prod _ fun e _ ↦ measurable_const.sub (measurable_edgeValue U e)
  have hprod_bdd : ∀ x : V → Ω, |∏ e ∈ starEdges v N, (1 - edgeValue U x e)| ≤ 1 := fun x ↦ by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun e _ ↦ abs_nonneg _) fun e _ ↦ by
      rw [abs_le]; constructor <;> linarith [edgeValue_nonneg U x e, edgeValue_le_one U x e]
  have hI1 := integrable_vertexProd_mul U δ v hprod_meas 1 hprod_bdd
  have hI2 := integrable_vertexProd_mul U δ v (f := fun _ ↦ (1 : ℝ)) measurable_const 1
    (fun _ ↦ by norm_num)
  have hI3 : ∀ e, Integrable (fun x ↦ vertexProd (evWeight U δ v) x * edgeValue U x e)
      (assignmentMeasure V μ) := fun e ↦
    integrable_vertexProd_mul U δ v (measurable_edgeValue U e) 1 fun x ↦ by
      rw [abs_of_nonneg (edgeValue_nonneg U x e)]; exact edgeValue_le_one U x e
  have hsplit : ∀ x, vertexProd (evWeight U δ v) x * psiV (H := H) U v x =
      vertexProd (evWeight U δ v) x * ∏ e ∈ starEdges v N, (1 - edgeValue U x e) -
        vertexProd (evWeight U δ v) x * 1 +
          ∑ e ∈ starEdges v N, vertexProd (evWeight U δ v) x * edgeValue U x e := by
    intro x; unfold psiV; rw [mul_add, mul_sub, Finset.mul_sum]
  have hA : Integrable (fun x ↦ vertexProd (evWeight U δ v) x *
      ∏ e ∈ starEdges v N, (1 - edgeValue U x e) - vertexProd (evWeight U δ v) x * 1)
      (assignmentMeasure V μ) := hI1.sub hI2
  have hB : Integrable (fun x ↦ ∑ e ∈ starEdges v N,
      vertexProd (evWeight U δ v) x * edgeValue U x e) (assignmentMeasure V μ) :=
    integrable_finsetSum _ fun e _ ↦ hI3 e
  rw [integral_congr_ae (ae_of_all _ hsplit), integral_add hA hB, integral_sub hI1 hI2,
    integral_finsetSum _ fun e _ ↦ hI3 e]
  -- identify the three kinds of terms
  have e1 : ∫ x, vertexProd (evWeight U δ v) x * ∏ e ∈ starEdges v N, (1 - edgeValue U x e)
      ∂assignmentMeasure V μ = (∫ y, indA U δ y * (t - gA U δ y) ^ k ∂μ) * t ^ (n - 1 - k) := by
    rw [← wInt_star_compl U δ v]
    unfold wInt edgeProd
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [edgeValue_compl]; ring
  have e2 : ∫ x, vertexProd (evWeight U δ v) x * 1 ∂assignmentMeasure V μ = s * t ^ (n - 1) := by
    rw [← wInt_none U δ v]
    unfold wInt edgeProd
    simp
  have e3 : ∀ w ∈ N, ∫ x, vertexProd (evWeight U δ v) x * edgeValue U x s(v, w)
      ∂assignmentMeasure V μ = (∫ y, indA U δ y * gA U δ y ∂μ) * t ^ (n - 2) := by
    intro w hw
    have hwv : w ≠ v := ne_of_mem_nbr hw
    rw [← wInt_single U δ v w hwv]
    unfold wInt edgeProd
    simp only [Finset.prod_singleton]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only []; ring
  have hinj : Set.InjOn (fun w ↦ s(v, w)) (N : Set V) := by
    intro w₁ h₁ w₂ h₂ h
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1.symm (ne_of_mem_nbr (Finset.mem_coe.mp h₂))
  rw [e1, e2, starEdges, Finset.sum_image hinj, Finset.sum_congr rfl e3, Finset.sum_const,
    H.card_neighborFinset_eq_degree, nsmul_eq_mul]
  -- combine into one integral against `1_A`
  have hgb := isBdd_gA U δ
  have hind := IsBdd.of_bddFun (indA U δ)
  have hpow_int : Integrable (fun y ↦ indA U δ y * (t - gA U δ y) ^ k) μ :=
    (hind.mul (((IsBdd.const t).sub hgb).pow k)).integrable
  have hg_int : Integrable (fun y ↦ indA U δ y * gA U δ y) μ := (hind.mul hgb).integrable
  have hs : s = ∫ y, indA U δ y ∂μ := rfl
  have hcomb : (∫ y, indA U δ y * (t - gA U δ y) ^ k ∂μ) * t ^ (n - 1 - k) - s * t ^ (n - 1) +
      (k : ℝ) * ((∫ y, indA U δ y * gA U δ y ∂μ) * t ^ (n - 2)) =
      ∫ y, indA U δ y * (t ^ (n - 1 - k) * (t - gA U δ y) ^ k - t ^ (n - 1) +
        k * t ^ (n - 1 - 1) * gA U δ y) ∂μ := by
    have h1 : Integrable (fun y ↦ indA U δ y * (t ^ (n - 1 - k) * (t - gA U δ y) ^ k)) μ :=
      (hind.mul ((IsBdd.const _).mul (((IsBdd.const t).sub hgb).pow k))).integrable
    have h2 : Integrable (fun y ↦ indA U δ y * t ^ (n - 1)) μ := hind.integrable.mul_const _
    have h3 : Integrable (fun y ↦ indA U δ y * ((k : ℝ) * t ^ (n - 1 - 1) * gA U δ y)) μ :=
      (hind.mul ((IsBdd.const _).mul hgb)).integrable
    have hfun : (fun y ↦ indA U δ y * (t ^ (n - 1 - k) * (t - gA U δ y) ^ k - t ^ (n - 1) +
        k * t ^ (n - 1 - 1) * gA U δ y)) = fun y ↦
        (indA U δ y * (t ^ (n - 1 - k) * (t - gA U δ y) ^ k) - indA U δ y * t ^ (n - 1)) +
          indA U δ y * ((k : ℝ) * t ^ (n - 1 - 1) * gA U δ y) := by
      funext y; ring
    have h12 : Integrable (fun y ↦ indA U δ y * (t ^ (n - 1 - k) * (t - gA U δ y) ^ k) -
        indA U δ y * t ^ (n - 1)) μ := h1.sub h2
    rw [hfun, integral_add h12 h3, integral_sub h1 h2]
    have i1 : ∫ y, indA U δ y * (t ^ (n - 1 - k) * (t - gA U δ y) ^ k) ∂μ =
        (∫ y, indA U δ y * (t - gA U δ y) ^ k ∂μ) * t ^ (n - 1 - k) := by
      rw [← integral_mul_const]; refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only []; ring
    have i2 : ∫ y, indA U δ y * t ^ (n - 1) ∂μ = s * t ^ (n - 1) := by
      rw [integral_mul_const]; rfl
    have i3 : ∫ y, indA U δ y * ((k : ℝ) * t ^ (n - 1 - 1) * gA U δ y) ∂μ =
        (k : ℝ) * ((∫ y, indA U δ y * gA U δ y ∂μ) * t ^ (n - 2)) := by
      rw [show n - 1 - 1 = n - 2 by omega, ← integral_mul_const, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only []; ring
    rw [i1, i2, i3]
  rw [hcomb, ← integral_const_mul]
  refine integral_mono ((hind.mul hgb.sq).integrable.const_mul _) ?_ fun y ↦ ?_
  · have : Integrable (fun y ↦ indA U δ y * (t ^ (n - 1 - k) * (t - gA U δ y) ^ k - t ^ (n - 1) +
        k * t ^ (n - 1 - 1) * gA U δ y)) μ :=
      (hind.mul ((((IsBdd.const _).mul (((IsBdd.const t).sub hgb).pow k)).sub (IsBdd.const _)).add
        ((IsBdd.const _).mul hgb))).integrable
    exact this
  · simp only []
    have hb := binom_ge (gA_nonneg U δ y) (gA_le_tA U δ y) hkn
    rw [show n - 1 - 2 = n - 3 by omega] at hb
    have hi := indBdd_nonneg (measurableSet_excSet U δ) y
    have := mul_le_mul_of_nonneg_left hb hi
    linarith

/-- **Proof of Proposition 4.15, bound on `D_H(U₁)`**:
`D_H(U₁) ≥ c_* t^{n-3} ∫_A g²`, i.e. `c_* (1-s)^{n-1} ∫_A h²` with `h = g/(1-s)`. -/
theorem Dfun_high_ge :
    (∑ v, ((H.degree v - 1 : ℕ) : ℝ)) * tA U δ ^ (Fintype.card V - 3) *
        ∫ y, indA U δ y * gA U δ y ^ 2 ∂μ ≤ Dfun H (highPart U δ) := by
  rw [Dfun_eq]
  have hle : ∀ x, ∑ v, vertexProd (evWeight U δ v) x * psiV (H := H) U v x ≤
      Dint H (highPart U δ) x := by
    intro x
    simp_rw [← vertexProd_mul_Dint_eq U δ]
    rw [← Finset.sum_mul]
    have h1 := sum_vertexProd_evWeight_le U δ x
    have h2 := Dint_nonneg (H := H) (highPart U δ) x
    have h3 : 0 ≤ ∑ v, vertexProd (evWeight U δ v) x :=
      Finset.sum_nonneg fun v _ ↦ vertexProd_evWeight_nonneg U δ v x
    nlinarith
  have hint : ∀ v, Integrable (fun x ↦ vertexProd (evWeight U δ v) x * psiV (H := H) U v x)
      (assignmentMeasure V μ) := by
    intro v
    refine integrable_vertexProd_mul U δ v ?_ (2 + (starEdges v (H.neighborFinset v)).card)
      fun x ↦ ?_
    · unfold psiV
      exact ((Finset.measurable_fun_prod _ fun e _ ↦ measurable_const.sub
        (measurable_edgeValue U e)).sub measurable_const).add
        (Finset.measurable_fun_sum _ fun e _ ↦ measurable_edgeValue U e)
    · unfold psiV
      have h1 : |∏ e ∈ starEdges v (H.neighborFinset v), (1 - edgeValue U x e)| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun e _ ↦ abs_nonneg _) fun e _ ↦ by
          rw [abs_le]; constructor <;> linarith [edgeValue_nonneg U x e, edgeValue_le_one U x e]
      have h2 : |∑ e ∈ starEdges v (H.neighborFinset v), edgeValue U x e| ≤
          (starEdges v (H.neighborFinset v)).card := by
        rw [abs_of_nonneg (Finset.sum_nonneg fun e _ ↦ edgeValue_nonneg U x e)]
        calc _ ≤ ∑ _e ∈ starEdges v (H.neighborFinset v), (1 : ℝ) :=
              Finset.sum_le_sum fun e _ ↦ edgeValue_le_one U x e
          _ = _ := by simp
      have := abs_add_le (∏ e ∈ starEdges v (H.neighborFinset v), (1 - edgeValue U x e) - 1)
        (∑ e ∈ starEdges v (H.neighborFinset v), edgeValue U x e)
      have := abs_sub (∏ e ∈ starEdges v (H.neighborFinset v), (1 - edgeValue U x e)) 1
      norm_num at *
      linarith
  calc (∑ v, ((H.degree v - 1 : ℕ) : ℝ)) * tA U δ ^ (Fintype.card V - 3) *
        ∫ y, indA U δ y * gA U δ y ^ 2 ∂μ
      = ∑ v, ((H.degree v - 1 : ℕ) : ℝ) * tA U δ ^ (Fintype.card V - 3) *
          ∫ y, indA U δ y * gA U δ y ^ 2 ∂μ := by rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ ∑ v, ∫ x, vertexProd (evWeight U δ v) x * psiV (H := H) U v x ∂assignmentMeasure V μ :=
        Finset.sum_le_sum fun v _ ↦ integral_event_ge U δ v
    _ = ∫ x, ∑ v, vertexProd (evWeight U δ v) x * psiV (H := H) U v x
          ∂assignmentMeasure V μ := (integral_finsetSum _ fun v _ ↦ hint v).symm
    _ ≤ ∫ x, Dint H (highPart U δ) x ∂assignmentMeasure V μ :=
        integral_mono (integrable_finsetSum _ fun v _ ↦ hint v) (integrable_Dint _) hle

end Events

end Taeyoung.Paper.Eventual
