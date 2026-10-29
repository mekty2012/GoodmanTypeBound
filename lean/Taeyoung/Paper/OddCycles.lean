import Taeyoung.Paper.Lifting
import OddCycleBound.Main
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Odd cycles and their clique joins (`paper.pdf`, Theorem 1.4, Corollary 1.5)

**Theorem 1.4.** For every odd `ℓ ≥ 3` and every graphon of edge density
`p > 1/2`, `t(C_ℓ,W) ≥ p^ℓ - p(1-p)^{ℓ-1} = Φ_{C_ℓ}(p)`.

The paper cites this theorem from Im, Kim, and Yang.  Their Lean formalization,
the Lake dependency `OddCycleBound`
(<https://github.com/mekty2012/OddCycleGoodman-lean>), proves the inequality for
every graphon and every odd `ℓ ≥ 3` (`OddCycleBound.odd_cycle_bound`).  It has
its own integral definitions of the edge density and of `t(C_ℓ,W)`, the trace of
the `ℓ`-fold kernel power, and this file is the bridge:

* `homDensity_cycleGraph`: for Mathlib's `cycleGraph ℓ` and `ℓ ≥ 3`,
  `homDensity (cycleGraph ℓ) W` is `OddCycleBound.cycleDensity`, by peeling the
  vertices of the cycle one at a time (`integral_pathWeight`);
* `edgeDensity_bridge`: the two edge densities agree.

Then `oddCycle_bound` is Theorem 1.4 in this project's vocabulary (for
every density, not just `p > 1/2`), and `cycleGraph_satisfiesLowerBound` is its
catalogue form.  On the chromatic side, `isChromaticPolynomial_cycleGraph` is
`P_{C_ℓ}(x) = (x-1)^ℓ + (-1)^ℓ (x-1)`, read off from the value of `t(C_ℓ, T_k)`
computed in `OddCycleBound` (`cycleDensity_completePartite`).

**Corollary 1.5.** For odd `ℓ ≥ 3` and `s ≥ 0`, `K_s ∨ C_ℓ` satisfies
the Goodman-type lower bound, i.e. `t(K_s ∨ C_ℓ, W) ≥ Φ_{K_s∨C_ℓ}(p)` for `p ≥ 1 - 1/(s+2)`
(`oddJoin_satisfiesLowerBound`).  `K_s ∨ C_ℓ` is `iterCone s (cycleGraph ℓ)`:
`s` successive universal vertices over the cycle.
-/

open MeasureTheory Polynomial Finset Filter

namespace Taeyoung.Paper

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal SimpleGraph

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The graphon interface of `OddCycleBound` -/

/-- A foundation graphon satisfies the graphon hypotheses of `OddCycleBound`. -/
theorem isGraphon_ofFoundation (W : Graphon Ω μ) : OddCycleBound.IsGraphon W.toFun μ where
  meas := W.measurable
  nonneg := W.nonneg
  le_one := W.le_one
  symm := W.symm

/-- The two edge densities agree. -/
theorem edgeDensity_bridge (W : Graphon Ω μ) :
    OddCycleBound.edgeDensity W.toFun μ = edgeDensity W := by
  show ∫ x, Taeyoung.degree W x ∂μ = cliqueDensity 2 W
  exact integral_degree W

/-! ### Path weights -/

/-- The weight of the path `a – y₀ – y₁ – ⋯ – y_{n-1} – b`. -/
noncomputable def pathWeight (W : Graphon Ω μ) : (n : ℕ) → Ω → Ω → (Fin n → Ω) → ℝ
  | 0, a, b, _ => W a b
  | n + 1, a, b, y => W a (y 0) * pathWeight W n (y 0) b (Fin.tail y)

omit [IsProbabilityMeasure μ] in
lemma pathWeight_nonneg (W : Graphon Ω μ) :
    ∀ (n : ℕ) (a b : Ω) (y : Fin n → Ω), 0 ≤ pathWeight W n a b y
  | 0, a, b, _ => W.nonneg a b
  | n + 1, a, b, y => mul_nonneg (W.nonneg _ _) (pathWeight_nonneg W n _ _ _)

omit [IsProbabilityMeasure μ] in
lemma pathWeight_le_one (W : Graphon Ω μ) :
    ∀ (n : ℕ) (a b : Ω) (y : Fin n → Ω), pathWeight W n a b y ≤ 1
  | 0, a, b, _ => W.le_one a b
  | n + 1, a, b, y => mul_le_one₀ (W.le_one _ _) (pathWeight_nonneg W n _ _ _)
      (pathWeight_le_one W n _ _ _)

omit [IsProbabilityMeasure μ] in
lemma measurable_pathWeight (W : Graphon Ω μ) :
    ∀ n : ℕ, Measurable fun q : Ω × Ω × (Fin n → Ω) ↦ pathWeight W n q.1 q.2.1 q.2.2
  | 0 => by
      simp only [pathWeight]
      exact W.measurable.comp (measurable_fst.prodMk measurable_snd.fst)
  | n + 1 => by
      simp only [pathWeight]
      have hy0 : Measurable fun q : Ω × Ω × (Fin (n + 1) → Ω) ↦ q.2.2 0 :=
        (measurable_pi_apply 0).comp measurable_snd.snd
      have htail : Measurable fun q : Ω × Ω × (Fin (n + 1) → Ω) ↦ Fin.tail q.2.2 :=
        measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i.succ).comp measurable_snd.snd
      have h1 : Measurable fun q : Ω × Ω × (Fin (n + 1) → Ω) ↦ W q.1 (q.2.2 0) :=
        W.measurable.comp (measurable_fst.prodMk hy0)
      have h2 : Measurable fun q : Ω × Ω × (Fin (n + 1) → Ω) ↦
          pathWeight W n (q.2.2 0) q.2.1 (Fin.tail q.2.2) :=
        (measurable_pathWeight W n).comp (hy0.prodMk (measurable_snd.fst.prodMk htail))
      exact h1.mul h2

omit [IsProbabilityMeasure μ] in
lemma measurable_pathWeight_right (W : Graphon Ω μ) (n : ℕ) (a b : Ω) :
    Measurable fun y : Fin n → Ω ↦ pathWeight W n a b y :=
  (measurable_pathWeight W n).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- **Integrating out the interior of a path gives the kernel power.** -/
theorem integral_pathWeight (W : Graphon Ω μ) :
    ∀ (n : ℕ) (a b : Ω), ∫ y, pathWeight W n a b y ∂assignmentMeasure (Fin n) μ =
      OddCycleBound.compPow μ W.toFun n a b
  | 0, a, b => by
      simp only [pathWeight, integral_const, probReal_univ, one_smul]
      rfl
  | n + 1, a, b => by
      rw [integral_assignmentMeasure_succ _ (measurable_pathWeight_right W (n + 1) a b)
        (C := 1) fun y ↦ by
          rw [abs_of_nonneg (pathWeight_nonneg W _ _ _ _)]
          exact pathWeight_le_one W _ _ _ _]
      simp only [pathWeight, Fin.cons_zero, Fin.tail_cons]
      simp_rw [integral_const_mul, integral_pathWeight W n]
      rfl

/-- The product along a path, with its last edge to `b`, is `pathWeight`. -/
lemma prod_path_eq_pathWeight (W : Graphon Ω μ) :
    ∀ (n : ℕ) (x : Fin (n + 1) → Ω) (b : Ω),
      (∏ i : Fin n, W (x i.castSucc) (x i.succ)) * W (x (Fin.last n)) b =
        pathWeight W n (x 0) b (Fin.tail x)
  | 0, x, b => by simp [pathWeight]
  | n + 1, x, b => by
      rw [Fin.prod_univ_succ]
      have ih := prod_path_eq_pathWeight W n (Fin.tail x) b
      simp only [Fin.tail] at ih
      simp only [pathWeight, Fin.tail]
      rw [← ih]
      simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero, Fin.succ_zero_eq_one]
      ring

/-! ### The cycle graph -/

/-- The edges of `C_{n+3}` are the pairs `{i, i+1}`. -/
lemma edgeFinset_cycleGraph (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset = univ.image fun i : Fin (n + 3) ↦ s(i, i + 1) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [mem_edgeFinset, mem_edgeSet, cycleGraph_adj, Finset.mem_image]
    constructor
    · rintro (h | h)
      · exact ⟨v, mem_univ _, by rw [Sym2.eq_swap]; congr 1; rw [← h]; abel⟩
      · exact ⟨u, mem_univ _, by congr 1; rw [← h]; abel⟩
    · rintro ⟨i, -, hi⟩
      rcases Sym2.eq_iff.mp hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; abel
      · left; abel

lemma cycleGraph_edge_injective (n : ℕ) :
    Function.Injective fun i : Fin (n + 3) ↦ s(i, i + 1) := by
  intro i j hij
  rcases Sym2.eq_iff.mp hij with ⟨h, -⟩ | ⟨h1, h2⟩
  · exact h
  · exfalso
    have h3 : j = j + (1 + 1) := by rw [← add_assoc, ← h1, h2]
    have h4 : (1 + 1 : Fin (n + 3)) = 0 := by
      have := congrArg (· - j) h3
      simpa using this.symm
    exact absurd h4 (ne_of_beq_false rfl)

lemma graphWeight_cycleGraph (W : Graphon Ω μ) (n : ℕ) (x : Fin (n + 3) → Ω) :
    graphWeight (cycleGraph (n + 3)) W x = ∏ i : Fin (n + 3), W (x i) (x (i + 1)) := by
  rw [graphWeight, edgeFinset_cycleGraph,
    Finset.prod_image fun i _ j _ h ↦ cycleGraph_edge_injective n h]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [edgeValue_mk]

lemma graphWeight_cycleGraph_eq_pathWeight (W : Graphon Ω μ) (n : ℕ)
    (x : Fin (n + 3) → Ω) :
    graphWeight (cycleGraph (n + 3)) W x = pathWeight W (n + 2) (x 0) (x 0) (Fin.tail x) := by
  rw [graphWeight_cycleGraph, Fin.prod_univ_castSucc]
  simp only [Fin.coeSucc_eq_succ, Fin.last_add_one]
  exact prod_path_eq_pathWeight W (n + 2) x (x 0)

/-- **`t(C_ℓ,W)` is the trace of the `ℓ`-th kernel power** (`OddCycleBound.cycleDensity`),
for `ℓ ≥ 3`. -/
theorem homDensity_cycleGraph (W : Graphon Ω μ) {m : ℕ} (hm : 3 ≤ m) :
    homDensity (cycleGraph m) W = OddCycleBound.cycleDensity μ W.toFun m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  rw [homDensity]
  simp_rw [graphWeight_cycleGraph_eq_pathWeight W n]
  have hg : Measurable fun x : Fin (n + 2 + 1) → Ω ↦ (x 0, x 0, Fin.tail x) :=
    (measurable_pi_apply 0).prodMk ((measurable_pi_apply 0).prodMk
      (measurable_pi_lambda _ fun i : Fin (n + 2) ↦ measurable_pi_apply i.succ))
  have hmeas : Measurable fun x : Fin (n + 2 + 1) → Ω ↦
      pathWeight W (n + 2) (x 0) (x 0) (Fin.tail x) :=
    (measurable_pathWeight W (n + 2)).comp hg
  rw [integral_assignmentMeasure_succ _ hmeas (C := 1) fun y ↦ by
    rw [abs_of_nonneg (pathWeight_nonneg W _ _ _ _)]
    exact pathWeight_le_one W _ _ _ _]
  simp only [Fin.cons_zero, Fin.tail_cons]
  simp_rw [integral_pathWeight W (n + 2)]
  rfl

/-! ### Theorem 1.4 -/

/-- **Theorem 1.4** (for every edge density): for odd `ℓ ≥ 3`,
`t(C_ℓ,W) ≥ p^ℓ - p(1-p)^{ℓ-1}`. -/
theorem oddCycle_bound (W : Graphon Ω μ) {ℓ : ℕ} (hodd : Odd ℓ) (h3 : 3 ≤ ℓ) :
    edgeDensity W ^ ℓ - edgeDensity W * (1 - edgeDensity W) ^ (ℓ - 1) ≤
      homDensity (cycleGraph ℓ) W := by
  have h := OddCycleBound.odd_cycle_bound (isGraphon_ofFoundation W) hodd h3
  rw [edgeDensity_bridge] at h
  rw [homDensity_cycleGraph W h3]
  exact h

/-! ### The chromatic polynomial of a cycle -/

/-- The two uniform measures on `Fin k` coincide. -/
lemma finiteUniformMeasure_eq_uniformFin (k : ℕ) [NeZero k] :
    finiteUniformMeasure (Fin k) = OddCycleBound.uniformFin k := by
  apply Measure.ext_iff_singleton.mpr
  intro a
  rw [finiteUniformMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
    PMF.uniformOfFintype_apply, OddCycleBound.uniformFin, Measure.smul_apply,
    Measure.count_singleton, smul_eq_mul, mul_one, Fintype.card_fin]

/-- `P_{C_m}(x) = (x-1)^m + (-1)^m (x-1)` for `m ≥ 3`. -/
theorem isChromaticPolynomial_cycleGraph {m : ℕ} (hm : 3 ≤ m) :
    IsChromaticPolynomial (cycleGraph m) ((X - 1) ^ m + C ((-1 : ℝ) ^ m) * (X - 1)) := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : properAssignmentCount (cycleGraph m) 0 = 0 := by
      classical
      rw [properAssignmentCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      exact (x ⟨0, by omega⟩).elim0
    rw [this]
    simp only [Nat.cast_zero, eval_add, eval_pow, eval_sub, eval_X, eval_one, eval_mul,
      eval_C, zero_sub]
    ring
  · haveI : NeZero k := ⟨hk.ne'⟩
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hdens := homDensity_balancedMultipartite (H := cycleGraph m) k
    rw [homDensity_cycleGraph _ hm] at hdens
    have hdens' : OddCycleBound.cycleDensity (finiteUniformMeasure (Fin k))
        (OddCycleBound.completePartite k) m =
        (properAssignmentCount (cycleGraph m) k : ℝ) / (k : ℝ) ^ Fintype.card (Fin m) := hdens
    have hval : OddCycleBound.cycleDensity (finiteUniformMeasure (Fin k))
        (OddCycleBound.completePartite k) m =
        ((k - 1 : ℝ) / k) ^ m + (k - 1 : ℝ) * (-1 / (k : ℝ)) ^ m := by
      rw [finiteUniformMeasure_eq_uniformFin]
      exact OddCycleBound.cycleDensity_completePartite (by omega) (by omega)
    rw [hval, Fintype.card_fin, eq_div_iff (pow_ne_zero _ hk')] at hdens'
    have e1 : ((k - 1 : ℝ) / k) ^ m * (k : ℝ) ^ m = (k - 1) ^ m := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hk')]
    have e2 : (-1 / (k : ℝ)) ^ m * (k : ℝ) ^ m = (-1) ^ m := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hk')]
    have hcount : (properAssignmentCount (cycleGraph m) k : ℝ) =
        (k - 1) ^ m + (k - 1) * (-1) ^ m := by
      rw [← hdens', add_mul, mul_assoc, e1, e2]
    rw [hcount]
    simp only [eval_add, eval_pow, eval_sub, eval_X, eval_one, eval_mul, eval_C]
    ring

/-- For odd `ℓ`, `Φ_{C_ℓ}(p) = p^ℓ - p(1-p)^{ℓ-1}` as a polynomial. -/
theorem targetPoly_cycleGraph {ℓ : ℕ} (hodd : Odd ℓ) (h3 : 3 ≤ ℓ) :
    targetPoly ℓ ((X - 1) ^ ℓ + C ((-1 : ℝ) ^ ℓ) * (X - 1)) =
      X * (X ^ (ℓ - 1) - (1 - X) ^ (ℓ - 1)) := by
  have hP := isChromaticPolynomial_cycleGraph h3
  apply Polynomial.funext
  intro z
  have h := chromaticTarget_eq_eval_targetPoly hP z
  simp only [Fintype.card_fin] at h
  rw [← h]
  obtain ⟨t, rfl⟩ := hodd
  have hsub : 2 * t + 1 - 1 = 2 * t := by omega
  rw [hsub]
  by_cases hz : z = 1
  · subst hz
    rw [chromaticTarget_at_one]
    simp only [eval_mul, eval_X, eval_sub, eval_pow, eval_one, sub_self, one_pow]
    rw [zero_pow (by omega)]
    ring
  · rw [chromaticTarget_of_ne_one _ hz, Fintype.card_fin]
    have hq : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    simp only [eval_add, eval_mul, eval_X, eval_sub, eval_pow, eval_one, eval_C]
    have h1 : 1 / (1 - z) - 1 = z / (1 - z) := by field_simp; ring
    rw [h1, Odd.neg_one_pow ⟨t, rfl⟩, div_pow, pow_succ (1 - z) (2 * t), pow_succ z (2 * t)]
    field_simp
    ring

/-- The profile of `Φ_{C_ℓ} = p(p^{ℓ-1} - (1-p)^{ℓ-1})` on `[1/2, 1]`. -/
theorem targetProfile_cycle (t : ℕ) :
    TargetProfile (X * (X ^ (2 * t + 2) - (1 - X) ^ (2 * t + 2))) (1 / 2) := by
  -- the three evaluations in closed form
  have e0 : ∀ z : ℝ, ((X : ℝ[X]) * (X ^ (2 * t + 2) - (1 - X) ^ (2 * t + 2))).eval z =
      z * (z ^ (2 * t + 2) - (1 - z) ^ (2 * t + 2)) := fun z ↦ by simp
  have e1 : ∀ z : ℝ, ((X : ℝ[X]) * (X ^ (2 * t + 2) - (1 - X) ^ (2 * t + 2))).derivative.eval z =
      (z ^ (2 * t + 2) - (1 - z) ^ (2 * t + 2)) +
        z * ((2 * t + 2) * (z ^ (2 * t + 1) + (1 - z) ^ (2 * t + 1))) := fun z ↦ by
    simp only [derivative_mul, derivative_X, derivative_sub, derivative_pow, derivative_one,
      eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_one, eval_C, eval_natCast,
      one_mul, zero_sub, eval_neg]
    push_cast
    ring
  have e2 : ∀ z : ℝ,
      ((X : ℝ[X]) * (X ^ (2 * t + 2) - (1 - X) ^ (2 * t + 2))).derivative.derivative.eval z =
      2 * ((2 * t + 2) * (z ^ (2 * t + 1) + (1 - z) ^ (2 * t + 1))) +
        z * ((2 * t + 2) * (2 * t + 1) * (z ^ (2 * t) - (1 - z) ^ (2 * t))) := fun z ↦ by
    simp only [derivative_mul, derivative_X, derivative_sub, derivative_add, derivative_pow,
      derivative_one, derivative_C, derivative_natCast, derivative_neg, neg_zero,
      eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_one, eval_C, eval_natCast,
      one_mul, zero_sub, eval_neg, zero_mul, eval_zero, mul_zero, zero_add, add_zero]
    push_cast
    ring
  -- `z ≥ 1/2` gives `z^j ≥ (1-z)^j`
  have hpow : ∀ (j : ℕ) (z : ℝ), 1 / 2 ≤ z → z ≤ 1 → (1 - z) ^ j ≤ z ^ j := fun j z h0 h1 ↦
    pow_le_pow_left₀ (by linarith) (by linarith) j
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0]; norm_num
  · intro z h0 h1
    rw [e0]
    have := hpow (2 * t + 2) z h0 h1
    exact mul_nonneg (by linarith) (by linarith)
  · intro z h0 h1
    rw [e1]
    have := hpow (2 * t + 2) z h0 h1
    have h1z : 0 ≤ 1 - z := by linarith
    have : 0 ≤ z ^ (2 * t + 1) + (1 - z) ^ (2 * t + 1) := by positivity
    have hz : 0 ≤ z := by linarith
    have : 0 ≤ z * ((2 * t + 2) * (z ^ (2 * t + 1) + (1 - z) ^ (2 * t + 1))) := by positivity
    linarith
  · intro z h0 h1
    rw [e2]
    have := hpow (2 * t) z h0 h1
    have h1z : 0 ≤ 1 - z := by linarith
    have hz : 0 ≤ z := by linarith
    have : 0 ≤ z ^ (2 * t + 1) + (1 - z) ^ (2 * t + 1) := by positivity
    have : 0 ≤ z ^ (2 * t) - (1 - z) ^ (2 * t) := by linarith
    positivity

/-- The chromatic number of an odd cycle is three. -/
theorem isChromaticNumber_cycleGraph_odd {ℓ : ℕ} (hodd : Odd ℓ) (h3 : 3 ≤ ℓ) :
    IsChromaticNumber (cycleGraph ℓ) 3 := by
  have hP := isChromaticPolynomial_cycleGraph h3
  have hval : ∀ k : ℕ, (properAssignmentCount (cycleGraph ℓ) k : ℝ) =
      ((k : ℝ) - 1) ^ ℓ - ((k : ℝ) - 1) := by
    intro k
    rw [← hP k]
    simp only [eval_add, eval_pow, eval_sub, eval_X, eval_one, eval_mul, eval_C,
      Odd.neg_one_pow hodd]
    ring
  refine ⟨?_, fun k hk ↦ ?_⟩
  · have h := hval 3
    have h2 : (2 : ℝ) ^ ℓ - 2 > 0 := by
      have : (2 : ℝ) ^ 3 ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) h3
      linarith
    have : (0 : ℝ) < properAssignmentCount (cycleGraph ℓ) 3 := by
      rw [h]; norm_num; linarith
    exact_mod_cast this
  · have h := hval k
    interval_cases k
    · have : (properAssignmentCount (cycleGraph ℓ) 0 : ℝ) = 0 := by
        rw [h]; norm_num [Odd.neg_one_pow hodd]
      exact_mod_cast this
    · have : (properAssignmentCount (cycleGraph ℓ) 1 : ℝ) = 0 := by
        rw [h]; norm_num [zero_pow (by omega : ℓ ≠ 0)]
      exact_mod_cast this
    · have : (properAssignmentCount (cycleGraph ℓ) 2 : ℝ) = 0 := by
        rw [h]; norm_num
      exact_mod_cast this

/-- **Theorem 1.4, catalogue form**: an odd cycle satisfies the
Goodman-type lower bound (`χ(C_ℓ) = 3`, so the interval is `p ≥ 1/2`). -/
theorem cycleGraph_satisfiesLowerBound {ℓ : ℕ} (hodd : Odd ℓ) (h3 : 3 ≤ ℓ) :
    SatisfiesLowerBound (cycleGraph ℓ) := by
  intro P r hP hr Ω _ μ _ W _
  rw [IsChromaticPolynomial.unique _ hP (isChromaticPolynomial_cycleGraph h3),
    chromaticTarget_eq_eval_targetPoly (isChromaticPolynomial_cycleGraph h3)]
  simp only [Fintype.card_fin]
  rw [targetPoly_cycleGraph hodd h3]
  have := oddCycle_bound W hodd h3
  simp only [eval_mul, eval_X, eval_sub, eval_pow, eval_one]
  have hsplit : edgeDensity W ^ ℓ = edgeDensity W * edgeDensity W ^ (ℓ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  rw [hsplit] at this
  linarith

/-! ### Corollary 1.5 -/

/-- **Corollary 1.5**: for odd `ℓ ≥ 3` and every `s ≥ 0`, the clique
join `K_s ∨ C_ℓ` satisfies the Goodman-type lower bound, i.e. the bound holds
whenever `p ≥ 1 - 1/(s + 2)`. -/
theorem oddJoin_satisfiesLowerBound {ℓ : ℕ} (hodd : Odd ℓ) (h3 : 3 ≤ ℓ) (s : ℕ) :
    SatisfiesLowerBound (iterCone s (cycleGraph ℓ)) := by
  have hP := isChromaticPolynomial_cycleGraph h3
  obtain ⟨t, ht⟩ := hodd
  have hprof : TargetProfile (targetPoly ℓ ((X - 1) ^ ℓ + C ((-1 : ℝ) ^ ℓ) * (X - 1)))
      (1 / 2) := by
    rw [targetPoly_cycleGraph ⟨t, ht⟩ h3]
    have : ℓ - 1 = 2 * (t - 1) + 2 := by omega
    rw [this]
    exact targetProfile_cycle (t - 1)
  have hbase : SatisfiesLowerBoundOn (cycleGraph ℓ) (Set.Ioi (1 / 2)) := fun Q hQ Ω _ μ _ W _ ↦
    cycleGraph_satisfiesLowerBound ⟨t, ht⟩ h3 Q 3 hQ (isChromaticNumber_cycleGraph_odd ⟨t, ht⟩ h3)
      W (by
        show 1 - 1 / (((3 - 1 : ℕ) : ℝ)) ≤ edgeDensity W
        norm_num
        linarith [show (1 / 2 : ℝ) < edgeDensity W from ‹_›])
  obtain ⟨hbound, -⟩ := iterated_lifting (by omega) (cycleGraph ℓ) hP (by norm_num) hprof hbase s
  have hthr : iterThreshold (1 / 2) s = 1 - 1 / ((((3 + s) - 1 : ℕ) : ℝ)) := by
    unfold iterThreshold
    congr 2
    rw [show 3 + s - 1 = s + 2 by omega]
    push_cast
    norm_num
  rw [hthr] at hbound
  exact (satisfiesLowerBound_iff_on
    (isChromaticNumber_iterCone _ (isChromaticNumber_cycleGraph_odd ⟨t, ht⟩ h3) s)).mpr hbound

end Taeyoung.Paper
