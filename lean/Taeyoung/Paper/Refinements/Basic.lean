import Taeyoung.Paper.Turan
import Taeyoung.Methods.Negative.Tensor
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Topology.Algebra.Polynomial

/-!
# Density ranges and Turán optimality: shared lemmas

`paper.pdf`, Section 5.1, records for each graph violating the
Goodman-type lower bound a range of edge densities on which the bound still
holds, and the integers `k` at which `T_k` is or is not optimal
(Table 1).  This file collects the general facts used to
read those entries off the certificates and counterexamples.

* `SatisfiesLowerBoundOn.Ici_of_Ioi`: a bound on `p > a` extends to `p = a`
  (`a < 1`).  Raising a graphon `W` of edge density `a` to
  `W + η(1-W)` moves its edge density above `a` and its `H`-density by at most
  `e(H)·η`; letting `η → 0` uses only the continuity of `Φ_H` at `a`.  This is
  what turns the strict threshold of Theorem 1.6 into the closed ranges
  `p ≥ 1 - (72·6¹²)⁻¹` of the table.
* `turanOptimal_of_satisfiesLowerBoundOn`: optimality of `T_k` is the bound at
  `p = 1 - 1/k`.
* `not_turanOptimal_of_lt`, `not_turanOptimal_of_tensor`: a graphon of edge
  density `1 - 1/k` with smaller `H`-density than `T_k`.
* `girth_eq_three_of_adj`: a graph with a triangle has girth `3`.
-/

open MeasureTheory Filter Topology

namespace Taeyoung.Paper.Refinements

open Taeyoung Taeyoung.Methods.PureChordal Taeyoung.Methods.Negative

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Girth three -/

omit [Fintype V] [DecidableEq V] in
/-- A graph containing a triangle has girth `3`. -/
theorem girth_eq_three_of_adj {H : SimpleGraph V} {a b c : V}
    (hab : H.Adj a b) (hbc : H.Adj b c) (hca : H.Adj c a) : H.girth = 3 := by
  let w : H.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  have hab' := H.ne_of_adj hab
  have hbc' := H.ne_of_adj hbc
  have hca' := H.ne_of_adj hca
  have hw : w.IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    constructor <;> simp [hab', hab'.symm, hbc', hca', hca'.symm]
  have h1 : H.girth ≤ 3 := H.girth_le_length hw
  have h2 : 3 ≤ H.girth := H.three_le_girth fun hacyc ↦ hacyc w hw
  omega

/-! ### Closing a strict density range -/

section Closure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `W + η(1-W)`: every value moved the fraction `η` of the way to `1`. -/
def _root_.Taeyoung.Graphon.raise (W : Graphon Ω μ) (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    Graphon Ω μ where
  toFun x y := W x y + η * (1 - W x y)
  measurable := W.measurable.add (measurable_const.mul (measurable_const.sub W.measurable))
  nonneg x y := by
    have := W.nonneg x y
    have := W.le_one x y
    nlinarith
  le_one x y := by
    have := W.nonneg x y
    have := W.le_one x y
    nlinarith
  symm x y := by
    show W x y + η * (1 - W x y) = W y x + η * (1 - W y x)
    rw [W.symm x y]

lemma edgeValue_raise (W : Graphon Ω μ) {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (x : V → Ω)
    (e : Sym2 V) :
    edgeValue (W.raise η h0 h1) x e = edgeValue W x e + η * (1 - edgeValue W x e) := by
  induction e using Sym2.inductionOn with
  | _ u v => rw [edgeValue_mk, edgeValue_mk]; rfl

/-- `∏ b - ∏ a ≤ ∑ (b - a)` for `0 ≤ a ≤ b ≤ 1`. -/
lemma prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i) (hb : ∀ i ∈ s, b i ≤ 1) :
    ∏ i ∈ s, b i - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (b i - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have ha' : ∀ i ∈ s, 0 ≤ a i := fun i hi ↦ ha i (Finset.mem_insert_of_mem hi)
    have hab' : ∀ i ∈ s, a i ≤ b i := fun i hi ↦ hab i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, b i ≤ 1 := fun i hi ↦ hb i (Finset.mem_insert_of_mem hi)
    have IH := ih ha' hab' hb'
    have hA1 : ∏ i ∈ s, a i ≤ 1 :=
      Finset.prod_le_one ha' fun i hi ↦ (hab' i hi).trans (hb' i hi)
    have hAB : ∏ i ∈ s, a i ≤ ∏ i ∈ s, b i := Finset.prod_le_prod ha' hab'
    have hjb : a j ≤ b j := hab j (Finset.mem_insert_self j s)
    have hj1 : b j ≤ 1 := hb j (Finset.mem_insert_self j s)
    nlinarith [mul_le_mul_of_nonneg_right hj1 (sub_nonneg.mpr hAB),
      mul_le_mul_of_nonneg_left hA1 (sub_nonneg.mpr hjb)]

lemma graphWeight_raise_le (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon Ω μ)
    {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (x : V → Ω) :
    graphWeight H (W.raise η h0 h1) x ≤ graphWeight H W x + H.edgeFinset.card * η := by
  have h := prod_sub_prod_le_sum H.edgeFinset (fun e ↦ edgeValue W x e)
    (fun e ↦ edgeValue (W.raise η h0 h1) x e) (fun e _ ↦ edgeValue_nonneg W x e)
    (fun e _ ↦ by
      rw [edgeValue_raise]
      nlinarith [edgeValue_le_one W x e])
    (fun e _ ↦ edgeValue_le_one _ x e)
  have hs : ∑ e ∈ H.edgeFinset, (edgeValue (W.raise η h0 h1) x e - edgeValue W x e) ≤
      ∑ _e ∈ H.edgeFinset, η :=
    Finset.sum_le_sum fun e _ ↦ by
      rw [edgeValue_raise]
      nlinarith [edgeValue_nonneg W x e]
  rw [Finset.sum_const, nsmul_eq_mul] at hs
  unfold graphWeight
  linarith

/-- Raising by `η` adds at most `e(H)·η` to the `H`-density. -/
lemma homDensity_raise_le (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon Ω μ)
    {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    homDensity H (W.raise η h0 h1) ≤ homDensity H W + H.edgeFinset.card * η := by
  unfold homDensity
  calc ∫ x, graphWeight H (W.raise η h0 h1) x ∂assignmentMeasure V μ
      ≤ ∫ x, (graphWeight H W x + H.edgeFinset.card * η) ∂assignmentMeasure V μ :=
        integral_mono (integrable_graphWeight H _)
          ((integrable_graphWeight H W).add (integrable_const _))
          (fun x ↦ graphWeight_raise_le H W h0 h1 x)
    _ = ∫ x, graphWeight H W x ∂assignmentMeasure V μ + H.edgeFinset.card * η := by
        rw [integral_add (integrable_graphWeight H W) (integrable_const _), integral_const]
        simp

/-- Raising by `η` takes the edge density `p` to `p + η(1-p)`. -/
lemma edgeDensity_raise (W : Graphon Ω μ) {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    edgeDensity (W.raise η h0 h1) = edgeDensity W + η * (1 - edgeDensity W) := by
  simp only [edgeDensity, cliqueDensity, homDensity]
  have hw : ∀ x : Fin 2 → Ω, graphWeight (⊤ : SimpleGraph (Fin 2)) (W.raise η h0 h1) x =
      (1 - η) * graphWeight ⊤ W x + η := fun x ↦ by
    rw [graphWeight_top_fin_two, graphWeight_top_fin_two]
    show W (x 0) (x 1) + η * (1 - W (x 0) (x 1)) = _
    ring
  simp_rw [hw]
  rw [integral_add ((integrable_graphWeight _ W).const_mul _) (integrable_const _),
    integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring

omit [Fintype V] [DecidableEq V] in
lemma continuousAt_chromaticTarget [Fintype V] (P : Polynomial ℝ) {p : ℝ} (hp : p ≠ 1) :
    ContinuousAt (chromaticTarget (V := V) P) p := by
  have h1 : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have hev : (fun q : ℝ ↦ (1 - q) ^ Fintype.card V * P.eval (1 / (1 - q))) =ᶠ[𝓝 p]
      chromaticTarget (V := V) P := by
    filter_upwards [isOpen_ne.mem_nhds hp] with q hq
    exact (chromaticTarget_of_ne_one P hq).symm
  refine ContinuousAt.congr ?_ hev
  have hinv : ContinuousAt (fun q : ℝ ↦ 1 / (1 - q)) p :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_id) h1
  exact ((continuousAt_const.sub continuousAt_id).pow _).mul
    (P.continuous.continuousAt.comp hinv)

end Closure

/-- **Closing a strict range.**  If the Goodman-type bound holds for every edge
density `p > a`, where `a < 1`, it also holds at `p = a`. -/
theorem SatisfiesLowerBoundOn.Ici_of_Ioi {H : SimpleGraph V} [DecidableRel H.Adj] {a : ℝ}
    (h : SatisfiesLowerBoundOn H (Set.Ioi a)) (ha : a < 1) :
    SatisfiesLowerBoundOn H (Set.Ici a) := by
  intro P hP Ω _ μ _ W hW
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hW) with heq | hlt
  · set p := edgeDensity W with hpdef
    set e : ℝ := (H.edgeFinset.card : ℝ)
    have hp1 : p < 1 := heq ▸ ha
    have key : ∀ η ∈ Set.Ioo (0 : ℝ) 1,
        chromaticTarget (V := V) P (p + η * (1 - p)) - e * η ≤ homDensity H W := by
      rintro η ⟨hη0, hη1⟩
      have hd := edgeDensity_raise W hη0.le hη1.le
      have hmem : edgeDensity (W.raise η hη0.le hη1.le) ∈ Set.Ioi a := by
        rw [hd, Set.mem_Ioi, ← hpdef, heq]
        nlinarith
      have h2 := h P hP (W.raise η hη0.le hη1.le) hmem
      rw [hd, ← hpdef] at h2
      have h3 := homDensity_raise_le H W hη0.le hη1.le
      linarith
    have hc : ContinuousAt
        (fun η : ℝ ↦ chromaticTarget (V := V) P (p + η * (1 - p)) - e * η) 0 := by
      have hinner : ContinuousAt (fun η : ℝ ↦ p + η * (1 - p)) 0 := by fun_prop
      have hct := continuousAt_chromaticTarget (V := V) P hp1.ne
      exact (hct.comp_of_eq hinner (by ring)).sub (continuousAt_const.mul continuousAt_id)
    have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ),
        chromaticTarget (V := V) P (p + η * (1 - p)) - e * η ≤ homDensity H W := by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with η hη using key η hη
    have := le_of_tendsto ht hev
    simpa using this
  · exact h P hP W hlt

/-- Edge densities never exceed `1`, so `[a, 1]` and `[a, ∞)` give the same bound. -/
theorem SatisfiesLowerBoundOn.Ici_of_Icc {H : SimpleGraph V} [DecidableRel H.Adj] {a : ℝ}
    (h : SatisfiesLowerBoundOn H (Set.Icc a 1)) : SatisfiesLowerBoundOn H (Set.Ici a) :=
  fun P hP _ _ _ _ W hW ↦ h P hP W ⟨hW, cliqueDensity_le_one 2 W⟩

theorem SatisfiesLowerBoundOn.union {H : SimpleGraph V} [DecidableRel H.Adj] {S T : Set ℝ}
    (hS : SatisfiesLowerBoundOn H S) (hT : SatisfiesLowerBoundOn H T) :
    SatisfiesLowerBoundOn H (S ∪ T) :=
  fun P hP _ _ _ _ W hW ↦ hW.elim (hS P hP W) (hT P hP W)

/-! ### Optimality of `T_k` -/

/-- `T_k` is optimal as soon as the bound holds at `p = 1 - 1/k`. -/
theorem turanOptimal_of_satisfiesLowerBoundOn {H : SimpleGraph V} [DecidableRel H.Adj]
    {S : Set ℝ} (h : SatisfiesLowerBoundOn H S) (k : ℕ) [NeZero k]
    (hk : 1 - 1 / (k : ℝ) ∈ S) : TuranOptimal H k :=
  (turanOptimal_iff_satisfiesLowerBoundOn k).mpr (h.mono (Set.singleton_subset_iff.mpr hk))

/-- The Turán densities increase with `k`. -/
theorem turanDensity_le {m k : ℕ} (hm : 0 < m) (hk : m ≤ k) :
    1 - 1 / (m : ℝ) ≤ 1 - 1 / (k : ℝ) := by
  have : 1 / (k : ℝ) ≤ 1 / m :=
    one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast hk)
  linarith

/-- `1 - 1/k ≥ a` for every `k ≥ m`, once `1 - 1/m ≥ a`. -/
theorem mem_Ici_turanDensity {m k : ℕ} (hm : 0 < m) (hk : m ≤ k) {a : ℝ}
    (ha : a ≤ 1 - 1 / (m : ℝ)) : 1 - 1 / (k : ℝ) ∈ Set.Ici a :=
  Set.mem_Ici.mpr (ha.trans (turanDensity_le hm hk))

/-- A graphon of edge density `1 - 1/k` with smaller `H`-density than `T_k`. -/
theorem not_turanOptimal_of_lt {H : SimpleGraph V} [DecidableRel H.Adj] {k : ℕ} [NeZero k]
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (hW : edgeDensity W = 1 - 1 / (k : ℝ))
    (hlt : homDensity H W < homDensity H (balancedMultipartiteGraphon k)) :
    ¬ TuranOptimal H k :=
  fun hopt ↦ absurd (hopt W hW) (not_le.mpr hlt)

/-- **A tensor witness.**  `T_a ⊗ T_b` of edge density `1 - 1/k` and
`P_H(a)·P_H(b)/(ab)^{v(H)} < P_H(k)/k^{v(H)}`. -/
theorem not_turanOptimal_of_tensor {H : SimpleGraph V} [DecidableRel H.Adj]
    (k a b : ℕ) [NeZero k] [NeZero a] [NeZero b]
    (hp : (1 - 1 / (a : ℝ)) * (1 - 1 / (b : ℝ)) = 1 - 1 / (k : ℝ))
    (hlt : (properAssignmentCount H a : ℝ) * properAssignmentCount H b /
        ((a : ℝ) * b) ^ Fintype.card V <
      properAssignmentCount H k / (k : ℝ) ^ Fintype.card V) :
    ¬ TuranOptimal H k := by
  refine not_turanOptimal_of_lt (tensorTuran a b) ?_ ?_
  · show cliqueDensity 2 (tensorTuran a b) = _
    rw [edgeDensity_tensorTuran, hp]
  · rw [homDensity_tensorTuran, homDensity_balancedMultipartite]
    exact hlt

/-- `T_{2k-1} ⊗ T_{2k}` has edge density `1 - 1/k`. -/
theorem tensorTuran_density_double (k : ℕ) (hk : 1 ≤ k) :
    (1 - 1 / ((2 * k - 1 : ℕ) : ℝ)) * (1 - 1 / ((2 * k : ℕ) : ℝ)) = 1 - 1 / (k : ℝ) := by
  have h1 : ((2 * k - 1 : ℕ) : ℝ) = 2 * k - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : (2 * (k : ℝ) - 1) ≠ 0 := by linarith
  have hb : (k : ℝ) ≠ 0 := by linarith
  rw [h1]
  push_cast
  field_simp
  ring

end Taeyoung.Paper.Refinements
