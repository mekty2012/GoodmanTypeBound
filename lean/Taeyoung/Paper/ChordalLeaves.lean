import Taeyoung.Paper.TriviallyPerfect
import Taeyoung.Methods.Peeling
import Mathlib.MeasureTheory.Integral.Pi

/-!
# A chordal graph failing the bound (`paper.pdf`, Proposition 6.1)

`L_m` is a triangle with `m` private pendant leaves attached to each of its three
vertices; here its vertex type is `Fin 3 ⊕ (Fin 3 × Fin m)`, the leaf `(r, t)`
hanging from the triangle vertex `r`.  The paper takes `m = 20`, a connected
chordal graph with `63` vertices and `63` edges.

* `isChromaticPolynomial_leafTriangle`: `P_{L_m}(x) = x (x-1)^{3m+1} (x-2)`, so
  `χ(L_m) = 3` and `Φ_{L_m}(p) = p^{3m+1}(2p - 1)`.
* `homDensity_leafTriangle`: integrating out the leaves,
  `t(L_m, W) = ∫∫∫ W(x,y)W(y,z)W(x,z) d(x)^m d(y)^m d(z)^m`.
* The witness: `[0,1] = A ⊔ B` with masses `2/5, 3/5`, `W = 0` on `A × A`, `1` on
  `A × B`, and `1/9` on `B × B` — here the two-point space `Fin 2` with those
  masses.  Its edge density is `13/25 ≥ 1/2` and its degrees are `3/5, 7/15`, so

  ```
  t(L₂₀, W) = 6/125 · (49/375)^20 + 1/3375 · (7/15)^60 < (13/25)^61 · (1/25) = Φ(13/25).
  ```

**Proposition 6.1.** `L₂₀` violates the Goodman-type lower bound
(`leafTriangle_twenty_violates`).
-/

open MeasureTheory Polynomial Finset
open scoped ENNReal

namespace Taeyoung.Paper

open Taeyoung Taeyoung.Methods

/-! ### The graph -/

/-- The oriented relation: triangle edges, and each leaf to its root. -/
def leafTriangleRel (m : ℕ) : Fin 3 ⊕ (Fin 3 × Fin m) → Fin 3 ⊕ (Fin 3 × Fin m) → Prop
  | Sum.inl a, Sum.inl b => a ≠ b
  | Sum.inl a, Sum.inr q => q.1 = a
  | Sum.inr _, _ => False

instance (m : ℕ) : DecidableRel (leafTriangleRel m)
  | Sum.inl a, Sum.inl b => inferInstanceAs (Decidable (a ≠ b))
  | Sum.inl a, Sum.inr q => inferInstanceAs (Decidable (q.1 = a))
  | Sum.inr _, _ => inferInstanceAs (Decidable False)

/-- **`L_m`**: a triangle with `m` private pendant leaves at each vertex. -/
def leafTriangle (m : ℕ) : SimpleGraph (Fin 3 ⊕ (Fin 3 × Fin m)) :=
  SimpleGraph.fromRel (leafTriangleRel m)

instance (m : ℕ) : DecidableRel (leafTriangle m).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

variable {m : ℕ}

@[simp] lemma leafTriangle_adj_inl_inl (a b : Fin 3) :
    (leafTriangle m).Adj (Sum.inl a) (Sum.inl b) ↔ a ≠ b := by
  simp only [leafTriangle, SimpleGraph.fromRel_adj, leafTriangleRel, ne_eq,
    Sum.inl.injEq]
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h; exact ⟨h, Or.inl h⟩

@[simp] lemma leafTriangle_adj_inl_inr (a : Fin 3) (q : Fin 3 × Fin m) :
    (leafTriangle m).Adj (Sum.inl a) (Sum.inr q) ↔ q.1 = a := by
  simp [leafTriangle, SimpleGraph.fromRel_adj, leafTriangleRel]

@[simp] lemma leafTriangle_adj_inr_inl (a : Fin 3) (q : Fin 3 × Fin m) :
    (leafTriangle m).Adj (Sum.inr q) (Sum.inl a) ↔ q.1 = a := by
  simp [leafTriangle, SimpleGraph.fromRel_adj, leafTriangleRel]

@[simp] lemma leafTriangle_adj_inr_inr (q q' : Fin 3 × Fin m) :
    ¬ (leafTriangle m).Adj (Sum.inr q) (Sum.inr q') := by
  simp [leafTriangle, SimpleGraph.fromRel_adj, leafTriangleRel]

/-! ### The chromatic polynomial -/

/-- Proper colourings: the triangle is injective and each leaf avoids its root. -/
lemma isProperAssignment_leafTriangle_iff {k : ℕ} (x : Fin 3 ⊕ (Fin 3 × Fin m) → Fin k) :
    IsProperAssignment (leafTriangle m) x ↔
      Function.Injective (fun a ↦ x (Sum.inl a)) ∧ ∀ q, x (Sum.inr q) ≠ x (Sum.inl q.1) := by
  constructor
  · intro h
    refine ⟨fun a b hab ↦ ?_, fun q hq ↦ ?_⟩
    · by_contra hne
      exact h ((leafTriangle_adj_inl_inl a b).mpr hne) hab
    · exact h ((leafTriangle_adj_inl_inr q.1 q).mpr rfl) hq.symm
  · rintro ⟨hinj, hleaf⟩ u v huv
    match u, v, huv with
    | Sum.inl a, Sum.inl b, huv =>
        exact fun h ↦ ((leafTriangle_adj_inl_inl a b).mp huv) (hinj h)
    | Sum.inl a, Sum.inr q, huv =>
        have : q.1 = a := (leafTriangle_adj_inl_inr a q).mp huv
        subst this
        exact fun h ↦ hleaf q h.symm
    | Sum.inr q, Sum.inl a, huv =>
        have : q.1 = a := (leafTriangle_adj_inr_inl a q).mp huv
        subst this
        exact fun h ↦ hleaf q h
    | Sum.inr q, Sum.inr q', huv => exact absurd huv (leafTriangle_adj_inr_inr q q')

/-- **The colouring count**: `k(k-1)(k-2) · (k-1)^{3m}`. -/
theorem properAssignmentCount_leafTriangle (k : ℕ) :
    properAssignmentCount (leafTriangle m) k = k.descFactorial 3 * (k - 1) ^ (3 * m) := by
  classical
  have hcard : properAssignmentCount (leafTriangle m) k =
      Fintype.card {x : Fin 3 ⊕ (Fin 3 × Fin m) → Fin k //
        IsProperAssignment (leafTriangle m) x} := by
    rw [properAssignmentCount, Fintype.card_subtype]
  rw [hcard]
  let e := Equiv.sumArrowEquivProdArrow (Fin 3) (Fin 3 × Fin m) (Fin k)
  have hsplit : Fintype.card {x : Fin 3 ⊕ (Fin 3 × Fin m) → Fin k //
        IsProperAssignment (leafTriangle m) x} =
      Fintype.card {p : (Fin 3 → Fin k) × (Fin 3 × Fin m → Fin k) //
        Function.Injective p.1 ∧ ∀ q, p.2 q ≠ p.1 q.1} := by
    refine Fintype.card_congr (Equiv.subtypeEquiv e fun x ↦ ?_)
    rw [isProperAssignment_leafTriangle_iff]
    rfl
  rw [hsplit, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ a : Fin 3 → Fin k,
      (∑ b : Fin 3 × Fin m → Fin k,
        if Function.Injective a ∧ ∀ q, b q ≠ a q.1 then 1 else 0) =
      if Function.Injective a then (k - 1) ^ (3 * m) else 0 := by
    intro a
    by_cases ha : Function.Injective a
    · simp only [ha, true_and, if_true]
      rw [← Finset.card_filter]
      have hset : (univ.filter fun b : Fin 3 × Fin m → Fin k ↦ ∀ q, b q ≠ a q.1) =
          Fintype.piFinset fun q ↦ univ.erase (a q.1) := by
        ext b
        simp [Fintype.mem_piFinset]
      rw [hset, Fintype.card_piFinset]
      simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, Finset.prod_const, Fintype.card_prod]
    · simp [ha]
  simp_rw [hinner]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq]
  simp

/-- **`P_{L_m}(x) = x(x-1)^{3m+1}(x-2)`.** -/
theorem isChromaticPolynomial_leafTriangle (m : ℕ) :
    IsChromaticPolynomial (leafTriangle m) (X * (X - 1) ^ (3 * m + 1) * (X - 2)) := by
  intro k
  rw [properAssignmentCount_leafTriangle]
  simp only [eval_mul, eval_X, eval_pow, eval_sub, eval_one, eval_ofNat]
  rcases Nat.lt_or_ge k 3 with hk | hk
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk]
    interval_cases k <;> simp
  · have h1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have hdesc : (k.descFactorial 3 : ℝ) = k * (k - 1) * (k - 2) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.descFactorial_succ, Nat.descFactorial_succ,
        Nat.descFactorial_one]
      push_cast [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_sub (show 1 ≤ k by omega)]
      ring
    push_cast [hdesc, h1]
    ring

theorem isChromaticNumber_leafTriangle (m : ℕ) : IsChromaticNumber (leafTriangle m) 3 where
  positive := by
    rw [properAssignmentCount_leafTriangle]
    positivity
  zero_below k hk := by
    rw [properAssignmentCount_leafTriangle, Nat.descFactorial_eq_zero_iff_lt.mpr hk, zero_mul]

/-- `Φ_{L_m}(p) = p^{3m+1}(2p - 1)`. -/
theorem chromaticTarget_leafTriangle (m : ℕ) (p : ℝ) :
    chromaticTarget (V := Fin 3 ⊕ (Fin 3 × Fin m))
        (X * (X - 1) ^ (3 * m + 1) * (X - 2)) p = p ^ (3 * m + 1) * (2 * p - 1) := by
  by_cases hp : p = 1
  · subst hp; norm_num
  · rw [chromaticTarget_of_ne_one _ hp]
    have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
    simp only [eval_mul, eval_X, eval_pow, eval_sub, eval_one, eval_ofNat]
    have hcard : Fintype.card (Fin 3 ⊕ (Fin 3 × Fin m)) = 1 + (3 * m + 1) + 1 := by
      simp; ring
    rw [hcard]
    have h1 : 1 / (1 - p) - 1 = p / (1 - p) := by field_simp; ring
    have h2 : 1 / (1 - p) - 2 = (2 * p - 1) / (1 - p) := by field_simp; ring
    rw [h1, h2, div_pow, pow_add, pow_add]
    field_simp

/-! ### The density, with the leaves integrated out -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The triangle edges, as an embedding. -/
def triEdge (m : ℕ) : Sym2 (Fin 3) ↪ Sym2 (Fin 3 ⊕ (Fin 3 × Fin m)) :=
  ⟨Sym2.map Sum.inl, Sym2.map.injective Sum.inl_injective⟩

/-- The leaf edges, as an embedding. -/
def leafEdge (m : ℕ) : (Fin 3 × Fin m) ↪ Sym2 (Fin 3 ⊕ (Fin 3 × Fin m)) :=
  ⟨fun q ↦ s(Sum.inl q.1, Sum.inr q), fun q q₁ h ↦ by
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · exact Sum.inr_injective h
    · exact absurd h (by simp)⟩

/-- The edges of `L_m`: the triangle edges and the leaf edges. -/
lemma edgeFinset_leafTriangle :
    (leafTriangle m).edgeFinset =
      ((⊤ : SimpleGraph (Fin 3)).edgeFinset.map (triEdge m)) ∪ (univ.map (leafEdge m)) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_union, Finset.mem_map,
      Finset.mem_map]
    rcases u with a | q <;> rcases v with b | q₁
    · rw [leafTriangle_adj_inl_inl]
      constructor
      · intro h
        left
        exact ⟨s(a, b), by rw [SimpleGraph.mem_edgeFinset]; exact h, by simp [triEdge]⟩
      · rintro (⟨e, he, hee⟩ | ⟨q, -, hq⟩)
        · induction e using Sym2.inductionOn with
          | _ c d =>
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at he
            simp only [triEdge, Function.Embedding.coeFn_mk, Sym2.map_mk, Sym2.eq_iff,
              Sum.inl.injEq] at hee
            rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact he
            · exact Ne.symm he
        · simp [leafEdge, Sym2.eq_iff] at hq
    · rw [leafTriangle_adj_inl_inr]
      constructor
      · intro h
        right
        exact ⟨q₁, Finset.mem_univ _, by simp [leafEdge, h]⟩
      · rintro (⟨e, -, hee⟩ | ⟨q₂, -, hq⟩)
        · induction e using Sym2.inductionOn with
          | _ c d => simp [triEdge, Sym2.eq_iff] at hee
        · simp only [leafEdge, Function.Embedding.coeFn_mk, Sym2.eq_iff, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, and_false, or_false] at hq
          obtain ⟨h1, rfl⟩ := hq
          exact h1
    · rw [leafTriangle_adj_inr_inl]
      constructor
      · intro h
        right
        exact ⟨q, Finset.mem_univ _, by simp [leafEdge, h, Sym2.eq_swap]⟩
      · rintro (⟨e, -, hee⟩ | ⟨q₂, -, hq⟩)
        · induction e using Sym2.inductionOn with
          | _ c d => simp [triEdge, Sym2.eq_iff] at hee
        · simp only [leafEdge, Function.Embedding.coeFn_mk, Sym2.eq_iff, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, false_and, false_or] at hq
          obtain ⟨h1, rfl⟩ := hq
          exact h1
    · simp only [leafTriangle_adj_inr_inr, false_iff, not_or]
      refine ⟨fun ⟨e, _, hee⟩ ↦ ?_, fun ⟨q₂, _, hq⟩ ↦ ?_⟩
      · induction e using Sym2.inductionOn with
        | _ c d => simp [triEdge, Sym2.eq_iff] at hee
      · simp [leafEdge, Sym2.eq_iff] at hq

/-- The weight of `L_m` is the triangle weight times one factor per leaf. -/
lemma graphWeight_leafTriangle (W : Graphon Ω μ) (x : Fin 3 ⊕ (Fin 3 × Fin m) → Ω) :
    graphWeight (leafTriangle m) W x =
      graphWeight (⊤ : SimpleGraph (Fin 3)) W (fun a ↦ x (Sum.inl a)) *
        ∏ q : Fin 3 × Fin m, W (x (Sum.inl q.1)) (x (Sum.inr q)) := by
  have hdisj : Disjoint ((⊤ : SimpleGraph (Fin 3)).edgeFinset.map (triEdge m))
      (univ.map (leafEdge m)) := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_map] at he he'
    obtain ⟨e', -, rfl⟩ := he
    obtain ⟨q, -, hq⟩ := he'
    induction e' using Sym2.inductionOn with
    | _ a b => simp [triEdge, leafEdge, Sym2.eq_iff] at hq
  rw [graphWeight, edgeFinset_leafTriangle, Finset.prod_union hdisj, Finset.prod_map,
    Finset.prod_map, graphWeight]
  have h1 : ∏ e ∈ (⊤ : SimpleGraph (Fin 3)).edgeFinset, edgeValue W x (triEdge m e) =
      ∏ e ∈ (⊤ : SimpleGraph (Fin 3)).edgeFinset, edgeValue W (fun a ↦ x (Sum.inl a)) e :=
    Finset.prod_congr rfl fun e _ ↦ edgeValue_sym2_map W x Sum.inl e
  have h2 : ∏ q ∈ (univ : Finset (Fin 3 × Fin m)), edgeValue W x (leafEdge m q) =
      ∏ q : Fin 3 × Fin m, W (x (Sum.inl q.1)) (x (Sum.inr q)) :=
    Finset.prod_congr rfl fun q _ ↦ by
      simp only [leafEdge, Function.Embedding.coeFn_mk, edgeValue_mk]
  rw [h1, h2]

/-- **Integrating out the leaves**: `t(L_m, W) = ∫ κ_{K₃}(x) d(x₀)^m d(x₁)^m d(x₂)^m`. -/
theorem homDensity_leafTriangle (W : Graphon Ω μ) :
    homDensity (leafTriangle m) W =
      ∫ a, graphWeight (⊤ : SimpleGraph (Fin 3)) W a *
        ∏ r : Fin 3, Taeyoung.degree W (a r) ^ m ∂assignmentMeasure (Fin 3) μ := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ (Fin 3 × Fin m) ↦ Ω)
  have hmp : MeasurePreserving e (assignmentMeasure (Fin 3 ⊕ (Fin 3 × Fin m)) μ)
      ((assignmentMeasure (Fin 3) μ).prod (assignmentMeasure (Fin 3 × Fin m) μ)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Fin 3 ⊕ (Fin 3 × Fin m) ↦ μ)
  let F : (Fin 3 → Ω) × (Fin 3 × Fin m → Ω) → ℝ := fun p ↦
    graphWeight (⊤ : SimpleGraph (Fin 3)) W p.1 * ∏ q : Fin 3 × Fin m, W (p.1 q.1) (p.2 q)
  have hF : ∀ x, graphWeight (leafTriangle m) W x = F (e x) := fun x ↦ by
    rw [graphWeight_leafTriangle]; rfl
  have hFm : Measurable F := by
    refine ((measurable_graphWeight _ W).comp measurable_fst).mul ?_
    refine Finset.measurable_prod _ fun q _ ↦ ?_
    have h1 : Measurable fun p : (Fin 3 → Ω) × (Fin 3 × Fin m → Ω) ↦ p.1 q.1 :=
      (measurable_pi_apply q.1).comp measurable_fst
    have h2 : Measurable fun p : (Fin 3 → Ω) × (Fin 3 × Fin m → Ω) ↦ p.2 q :=
      (measurable_pi_apply q).comp measurable_snd
    exact W.measurable.comp (h1.prodMk h2)
  have hFb : ∀ p, |F p| ≤ 1 := fun p ↦ by
    have h0 : 0 ≤ ∏ q : Fin 3 × Fin m, W (p.1 q.1) (p.2 q) :=
      Finset.prod_nonneg fun q _ ↦ W.nonneg _ _
    have h1 : ∏ q : Fin 3 × Fin m, W (p.1 q.1) (p.2 q) ≤ 1 :=
      Finset.prod_le_one (fun q _ ↦ W.nonneg _ _) fun q _ ↦ W.le_one _ _
    rw [abs_of_nonneg (mul_nonneg (graphWeight_nonneg _ W _) h0)]
    exact mul_le_one₀ (graphWeight_le_one _ W _) h0 h1
  have hFi : Integrable F
      ((assignmentMeasure (Fin 3) μ).prod (assignmentMeasure (Fin 3 × Fin m) μ)) :=
    (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
      (ae_of_all _ fun p ↦ by rw [Real.norm_eq_abs]; exact hFb p)
  rw [homDensity, integral_congr_ae (ae_of_all _ hF), hmp.integral_comp' (g := F),
    integral_prod F hFi]
  refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
  simp only [F]
  rw [integral_const_mul]
  congr 1
  rw [assignmentMeasure,
    integral_fintype_prod_eq_prod (fun q : Fin 3 × Fin m ↦ fun y ↦ W (a q.1) y),
    Fintype.prod_prod_type]
  simp [Taeyoung.degree, Finset.prod_const]

/-! ### The witness -/

/-- The masses `2/5, 3/5`. -/
noncomputable def twoPointMass : Fin 2 → ℝ≥0∞ := ![ENNReal.ofReal (2 / 5), ENNReal.ofReal (3 / 5)]

lemma twoPointMass_sum : ∑ i, twoPointMass i = 1 := by
  rw [Fin.sum_univ_two]
  simp only [twoPointMass, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- The two-point probability space `{A, B}` with masses `2/5` and `3/5`. -/
noncomputable def twoPoint : Measure (Fin 2) :=
  (PMF.ofFintype twoPointMass twoPointMass_sum).toMeasure

instance : IsProbabilityMeasure twoPoint := by
  unfold twoPoint; infer_instance

lemma integral_twoPoint (f : Fin 2 → ℝ) : ∫ x, f x ∂twoPoint = 2 / 5 * f 0 + 3 / 5 * f 1 := by
  rw [twoPoint, PMF.integral_eq_sum, Fin.sum_univ_two]
  simp only [PMF.ofFintype_apply, twoPointMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]

/-- `W = 0` on `A × A`, `1` on `A × B`, `1/9` on `B × B`. -/
noncomputable def witnessVal : Fin 2 → Fin 2 → ℝ := ![![0, 1], ![1, 1 / 9]]

/-- The witness graphon. -/
noncomputable def witness : Graphon (Fin 2) twoPoint where
  toFun := witnessVal
  measurable := measurable_of_finite _
  nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num [witnessVal]
  le_one i j := by fin_cases i <;> fin_cases j <;> norm_num [witnessVal]
  symm i j := by fin_cases i <;> fin_cases j <;> rfl

lemma degree_witness (i : Fin 2) :
    Taeyoung.degree witness i = ![3 / 5, 7 / 15] i := by
  rw [Taeyoung.degree, integral_twoPoint]
  fin_cases i <;> norm_num [witness, witnessVal]

lemma edgeDensity_witness : edgeDensity witness = 13 / 25 := by
  rw [edgeDensity, ← integral_degree, integral_twoPoint, degree_witness, degree_witness]
  norm_num

lemma homDensity_witness :
    homDensity (leafTriangle m) witness =
      6 / 125 * (3 / 5) ^ m * (7 / 15) ^ (2 * m) + 1 / 3375 * (7 / 15) ^ (3 * m) := by
  rw [homDensity_leafTriangle]
  have hE : (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      revert u v
      decide
  have hK3 : ∀ a : Fin 3 → Fin 2, graphWeight (⊤ : SimpleGraph (Fin 3)) witness a *
      ∏ r : Fin 3, Taeyoung.degree witness (a r) ^ m =
      witness (a 0) (a 1) * witness (a 0) (a 2) * witness (a 1) (a 2) *
        (Taeyoung.degree witness (a 0) ^ m * Taeyoung.degree witness (a 1) ^ m *
          Taeyoung.degree witness (a 2) ^ m) := by
    intro a
    rw [graphWeight, hE, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton, Fin.prod_univ_three]
    simp only [edgeValue_mk]
    ring
  simp_rw [hK3]
  have hd : ∀ i, Taeyoung.degree witness i ^ m ≤ 1 := fun i ↦
    pow_le_one₀ (Taeyoung.degree_nonneg _ _) (Taeyoung.degree_le_one _ _)
  have hpeel := Methods.integral_assignment_fin_three (μ := twoPoint)
    (g := fun a0 a1 a2 ↦ witness a0 a1 * witness a0 a2 * witness a1 a2 *
      (Taeyoung.degree witness a0 ^ m * Taeyoung.degree witness a1 ^ m *
        Taeyoung.degree witness a2 ^ m)) (measurable_of_finite _) (fun y ↦ by
      have h1 := witness.nonneg (y 0) (y 1)
      have h2 := witness.nonneg (y 0) (y 2)
      have h3 := witness.nonneg (y 1) (y 2)
      have d0 := Taeyoung.degree_nonneg witness (y 0)
      have d1 := Taeyoung.degree_nonneg witness (y 1)
      have d2 := Taeyoung.degree_nonneg witness (y 2)
      rw [abs_of_nonneg (by positivity)]
      have e1 := witness.le_one (y 0) (y 1)
      have e2 := witness.le_one (y 0) (y 2)
      have e3 := witness.le_one (y 1) (y 2)
      exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ e1 h2 e2) h3 e3) (by positivity)
        (mul_le_one₀ (mul_le_one₀ (hd _) (by positivity) (hd _)) (by positivity) (hd _)))
  try simp only at hpeel
  rw [hpeel]
  have hw : ∀ i j : Fin 2, witness i j = witnessVal i j := fun _ _ ↦ rfl
  simp only [integral_twoPoint, degree_witness, hw]
  simp only [witnessVal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- **Proposition 6.1**: the chordal graph `L₂₀` (a triangle with
twenty private pendant leaves at each vertex) violates the Goodman-type lower
bound.  At the witness, `p = 13/25` and
`t(L₂₀,W) = 6/125·(49/375)^20 + 1/3375·(7/15)^60 < (13/25)^61/25 = Φ(13/25)`. -/
theorem leafTriangle_twenty_violates : ViolatesLowerBound (leafTriangle 20) := by
  intro hsat
  have h := hsat _ 3 (isChromaticPolynomial_leafTriangle 20) (isChromaticNumber_leafTriangle 20)
    witness (by rw [admissibleDensity, edgeDensity_witness]; norm_num)
  rw [chromaticTarget_leafTriangle, edgeDensity_witness, homDensity_witness] at h
  norm_num at h

end Taeyoung.Paper
