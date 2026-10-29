import Taeyoung.Paper.TargetPolynomial
import Taeyoung.Methods.PureChordal.Main

/-!
# Padding a clique tree to equal bag sizes (`paper.pdf`, Section 2)

Let `D` be a maximal-clique tree of `H` whose bags have sizes `r_i ≤ k`.  Adjoin,
for each bag `i`, `k - r_i` new *private* vertices joined to each other and to
the whole bag.  The result `extGraph D k` is a chordal graph all of whose bags
`extBag D k i` have size `k`, with the same tree, the same parents and the same
separators; `extDecomp D k` is that pure clique-tree certificate.

Two uses are made of it.

* **Chromatic side.**  Colouring the padding of bag `i` injectively, away from
  the `r_i` colours of `C_i`, gives
  `P_{H'}(x) = P_H(x) ∏_i (x - r_i)_{(k - r_i)}` (`properAssignmentCount_extGraph`).
  Combined with the pure factorization of `P_{H'}` this yields the factorization
  of Section 2, `P_H(x) = ∏_i ∏_{s_i ≤ j < r_i} (x - j)`
  (`isChromaticPolynomial_profilePoly`).  The paper's regrouping
  `∏_{j=1}^k (x - j + 1)^{b_j}`, which reads `b_j` as the multiplicity of the root
  `j - 1`, is not stated separately in Lean.
* **Analytic side** (`Paper/Profile/Gluing.lean`): the junction law of the pure
  certificate has every bag law equal to `κ_k/t_k`, so its marginal on `C_i` is the
  marginal `ρ_{r_i}` of `ρ_k`, exactly the law the paper glues.
-/

open Finset Polynomial

namespace Taeyoung.Paper.Profile

open Taeyoung Taeyoung.Methods.PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} {m : ℕ}

/-! ### Bag and separator sizes -/

/-- The parent separator of bag `i` (empty at the root). -/
def sep (D : MaximalCliqueTreeDecomp H m) (i : Fin m) : Finset V :=
  if i = D.root then ∅ else D.bag i ∩ D.bag (D.parent i)

lemma sep_subset_bag (D : MaximalCliqueTreeDecomp H m) (i : Fin m) : sep D i ⊆ D.bag i := by
  unfold sep; split_ifs
  · exact Finset.empty_subset _
  · exact Finset.inter_subset_left

/-- `r_i = |C_i|`. -/
def r (D : MaximalCliqueTreeDecomp H m) (i : Fin m) : ℕ := (D.bag i).card

/-- `s_i = |S_i|`. -/
def s (D : MaximalCliqueTreeDecomp H m) (i : Fin m) : ℕ := (sep D i).card

lemma s_le_r (D : MaximalCliqueTreeDecomp H m) (i : Fin m) : s D i ≤ r D i :=
  Finset.card_le_card (sep_subset_bag D i)

/-! ### The padded graph -/

/-- Padding vertices: `k - r_i` of them for bag `i`. -/
abbrev Pad (D : MaximalCliqueTreeDecomp H m) (k : ℕ) : Type :=
  Σ i : Fin m, Fin (k - (D.bag i).card)

/-- The padded vertex set. -/
abbrev ExtV (D : MaximalCliqueTreeDecomp H m) (k : ℕ) : Type _ := V ⊕ Pad D k

variable (D : MaximalCliqueTreeDecomp H m) (k : ℕ)

/-- The padding of bag `i`. -/
def padOf (i : Fin m) : Finset (Pad D k) := univ.filter fun e ↦ e.1 = i

lemma mem_padOf {i : Fin m} {e : Pad D k} : e ∈ padOf D k i ↔ e.1 = i := by
  simp [padOf]

lemma card_padOf (i : Fin m) : (padOf D k i).card = k - (D.bag i).card := by
  have : padOf D k i = (univ : Finset (Fin (k - (D.bag i).card))).map
      ⟨Sigma.mk i, sigma_mk_injective⟩ := by
    ext ⟨j, t⟩
    simp only [mem_padOf, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl; exact ⟨t, rfl⟩
    · rintro ⟨t', h⟩; exact (congrArg Sigma.fst h).symm
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The padded bag `C_i ⊔ pad_i`. -/
def extBag (i : Fin m) : Finset (ExtV D k) := (D.bag i).disjSum (padOf D k i)

@[simp] lemma inl_mem_extBag {i : Fin m} {v : V} :
    (Sum.inl v : ExtV D k) ∈ extBag D k i ↔ v ∈ D.bag i := Finset.inl_mem_disjSum

@[simp] lemma inr_mem_extBag {i : Fin m} {e : Pad D k} :
    (Sum.inr e : ExtV D k) ∈ extBag D k i ↔ e.1 = i := by
  rw [extBag, Finset.inr_mem_disjSum, mem_padOf]

/-- The padded graph: every padded bag is a clique, and nothing else. -/
def extGraph : SimpleGraph (ExtV D k) :=
  SimpleGraph.fromRel fun u v ↦ ∃ i, u ∈ extBag D k i ∧ v ∈ extBag D k i

noncomputable instance : DecidableRel (extGraph D k).Adj := Classical.decRel _

lemma extGraph_adj {u v : ExtV D k} :
    (extGraph D k).Adj u v ↔ u ≠ v ∧ ∃ i, u ∈ extBag D k i ∧ v ∈ extBag D k i := by
  rw [extGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, ⟨i, hu, hv⟩ | ⟨i, hv, hu⟩⟩ <;> exact ⟨h, i, hu, hv⟩
  · rintro ⟨h, i, hu, hv⟩; exact ⟨h, Or.inl ⟨i, hu, hv⟩⟩

/-- On the original vertices the padded graph is `H`. -/
lemma extGraph_adj_inl {u v : V} :
    (extGraph D k).Adj (Sum.inl u) (Sum.inl v) ↔ H.Adj u v := by
  rw [extGraph_adj]
  constructor
  · rintro ⟨h, i, hu, hv⟩
    rw [inl_mem_extBag] at hu hv
    exact (D.bag_maximal i).1 hu hv (fun huv ↦ h (by rw [huv]))
  · intro h
    obtain ⟨i, hu, hv⟩ := D.edge_cover h
    exact ⟨fun he ↦ h.ne (Sum.inl_injective he), i, by simpa using hu, by simpa using hv⟩

variable {D k}

lemma card_extBag (hk : ∀ i, (D.bag i).card ≤ k) (i : Fin m) : (extBag D k i).card = k := by
  rw [extBag, Finset.card_disjSum, card_padOf]
  have := hk i
  omega

lemma extBag_injective : Function.Injective (extBag D k) := by
  intro i j hij
  apply D.bag_injective
  ext v
  have := congrArg (fun S : Finset (ExtV D k) ↦ (Sum.inl v : ExtV D k) ∈ S) hij
  simpa using this

/-- The bags of the padded tree intersect exactly as the original ones. -/
lemma extBag_inter (i j : Fin m) (hij : i ≠ j) :
    extBag D k i ∩ extBag D k j = (D.bag i ∩ D.bag j).disjSum ∅ := by
  ext x
  rcases x with v | e
  · simp
  · simp only [Finset.mem_inter, inr_mem_extBag, Finset.inr_mem_disjSum, Finset.notMem_empty,
      iff_false, not_and]
    intro h1 h2
    exact hij (h1.symm.trans h2)

variable (D k)

/-- **The padded pure clique tree.** -/
def extDecomp (hk : ∀ i, (D.bag i).card ≤ k) : PureCliqueTreeDecomp (extGraph D k) k m where
  root := D.root
  root_val := D.root_val
  parent := D.parent
  parent_lt := D.parent_lt
  parent_root := D.parent_root
  bag := extBag D k
  bag_card := card_extBag hk
  bag_clique i := by
    intro u hu v hv huv
    exact (extGraph_adj D k).mpr ⟨huv, i, hu, hv⟩
  bag_injective := extBag_injective
  vertex_cover := by
    intro x
    rcases x with v | e
    · obtain ⟨i, hi⟩ := D.vertex_cover v
      exact ⟨i, by simpa using hi⟩
    · exact ⟨e.1, by simp⟩
  edge_cover := by
    intro u v huv
    obtain ⟨-, i, hu, hv⟩ := (extGraph_adj D k).mp huv
    exact ⟨i, hu, hv⟩
  old_eq_parentSeparator := by
    intro i hi
    have hD := D.old_eq_parentSeparator i hi
    ext x
    rcases x with v | e
    · have := congrArg (fun S : Finset V ↦ v ∈ S) hD
      simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
        true_and, eq_iff_iff] at this
      simpa [Finset.mem_inter, Finset.mem_biUnion] using this
    · simp only [Finset.mem_inter, inr_mem_extBag, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, j, hj, h2⟩
        exfalso
        rw [← h1, ← h2] at hj
        exact Nat.lt_irrefl _ hj
      · rintro ⟨h1, h2⟩
        exfalso
        have hlt := D.parent_lt i hi
        have hpi : D.parent i = i := h2.symm.trans h1
        rw [hpi] at hlt
        exact Nat.lt_irrefl _ hlt

lemma extDecomp_bag (hk : ∀ i, (D.bag i).card ≤ k) (i : Fin m) :
    (extDecomp D k hk).bag i = extBag D k i := rfl

/-- The separators of the padded tree are those of `D`. -/
lemma extDecomp_separator (hk : ∀ i, (D.bag i).card ≤ k) (i : Fin m) :
    (extDecomp D k hk).separator i = (sep D i).disjSum ∅ := by
  unfold PureCliqueTreeDecomp.separator sep
  by_cases hi : i = D.root
  · have h1 : i = (extDecomp D k hk).root := hi
    rw [if_pos h1, if_pos hi]
    ext x
    rcases x with v | e <;> simp
  · have h1 : ¬ i = (extDecomp D k hk).root := hi
    rw [if_neg h1, if_neg hi]
    have hne : i ≠ D.parent i := by
      intro h
      have := D.parent_lt i hi
      rw [← h] at this
      exact Nat.lt_irrefl _ this
    exact extBag_inter i (D.parent i) hne

lemma extDecomp_sepCard (hk : ∀ i, (D.bag i).card ≤ k) (i : Fin m) :
    (extDecomp D k hk).sepCard i = s D i := by
  rw [PureCliqueTreeDecomp.sepCard, extDecomp_separator, Finset.card_disjSum,
    Finset.card_empty, add_zero, s]

/-! ### Colourings of the padded graph -/

/-- Injective colourings of `a` points avoiding a set of `r` colours. -/
lemma card_injective_avoiding {c a : ℕ} (S : Finset (Fin c)) :
    ((univ : Finset (Fin a → Fin c)).filter
      fun w ↦ Function.Injective w ∧ ∀ t, w t ∉ S).card = (c - S.card).descFactorial a := by
  classical
  rw [← Fintype.card_subtype]
  have e : {w : Fin a → Fin c // Function.Injective w ∧ ∀ t, w t ∉ S} ≃
      (Fin a ↪ {x : Fin c // x ∉ S}) :=
    { toFun := fun w ↦ ⟨fun t ↦ ⟨w.1 t, w.2.2 t⟩, fun t t' h ↦ w.2.1 (congrArg Subtype.val h)⟩
      invFun := fun f ↦ ⟨fun t ↦ (f t).1, fun t t' h ↦ f.injective (Subtype.ext h),
        fun t ↦ (f t).2⟩
      left_inv := fun w ↦ rfl
      right_inv := fun f ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_coe]

variable [DecidableRel H.Adj]

/-- Proper colourings of the padded graph, split into the original vertices and
the paddings. -/
lemma isProperAssignment_extGraph_iff {c : ℕ} (x : ExtV D k → Fin c) :
    IsProperAssignment (extGraph D k) x ↔
      IsProperAssignment H (fun v ↦ x (Sum.inl v)) ∧
        ∀ i : Fin m, Function.Injective (fun t : Fin (k - (D.bag i).card) ↦ x (Sum.inr ⟨i, t⟩)) ∧
          ∀ t, x (Sum.inr ⟨i, t⟩) ∉ (D.bag i).image fun v ↦ x (Sum.inl v) := by
  constructor
  · intro hx
    refine ⟨fun u v huv ↦ hx ((extGraph_adj_inl D k).mpr huv), fun i ↦ ⟨?_, ?_⟩⟩
    · intro t t' htt
      by_contra hne
      exact hx ((extGraph_adj D k).mpr ⟨fun h ↦ hne (by simpa using h), i, by simp, by simp⟩) htt
    · intro t hmem
      obtain ⟨v, hv, hxv⟩ := Finset.mem_image.mp hmem
      exact hx ((extGraph_adj D k).mpr ⟨fun h ↦ by simp at h, i, by simpa using hv, by simp⟩)
        hxv
  · rintro ⟨hH, hpad⟩ a b hab
    obtain ⟨hne, i, ha, hb⟩ := (extGraph_adj D k).mp hab
    rcases a with u | ⟨j, t⟩ <;> rcases b with v | ⟨j', t'⟩
    · exact hH ((extGraph_adj_inl D k).mp hab)
    · rw [inl_mem_extBag] at ha
      rw [inr_mem_extBag] at hb
      subst hb
      intro h
      exact (hpad j').2 t' (Finset.mem_image.mpr ⟨u, ha, h⟩)
    · rw [inr_mem_extBag] at ha
      rw [inl_mem_extBag] at hb
      subst ha
      intro h
      exact (hpad j).2 t (Finset.mem_image.mpr ⟨v, hb, h.symm⟩)
    · rw [inr_mem_extBag] at ha hb
      subst ha hb
      intro h
      have : t = t' := (hpad _).1 h
      exact hne (by rw [this])

/-- **`P_{H'}(c) = P_H(c) ∏_i (c - r_i)_{(k - r_i)}`.** -/
theorem properAssignmentCount_extGraph (c : ℕ) :
    properAssignmentCount (extGraph D k) c =
      properAssignmentCount H c *
        ∏ i : Fin m, (c - (D.bag i).card).descFactorial (k - (D.bag i).card) := by
  classical
  -- split `ExtV → Fin c` into the original part and the padding part
  let e₁ := Equiv.sumArrowEquivProdArrow V (Pad D k) (Fin c)
  let e₂ : (Pad D k → Fin c) ≃ ((i : Fin m) → Fin (k - (D.bag i).card) → Fin c) :=
    Equiv.piCurry fun _ _ ↦ Fin c
  have hcount : properAssignmentCount (extGraph D k) c =
      Fintype.card {p : (V → Fin c) × ((i : Fin m) → Fin (k - (D.bag i).card) → Fin c) //
        IsProperAssignment H p.1 ∧ ∀ i, Function.Injective (p.2 i) ∧
          ∀ t, p.2 i t ∉ (D.bag i).image p.1} := by
    rw [properAssignmentCount, ← Fintype.card_subtype]
    refine Fintype.card_congr ((Equiv.subtypeEquiv (e₁.trans (Equiv.prodCongr (Equiv.refl _) e₂))
      fun x ↦ ?_))
    rw [isProperAssignment_extGraph_iff]
    rfl
  rw [hcount, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ y : V → Fin c,
      (∑ z : (i : Fin m) → Fin (k - (D.bag i).card) → Fin c,
        if IsProperAssignment H y ∧ ∀ i, Function.Injective (z i) ∧
          ∀ t, z i t ∉ (D.bag i).image y then 1 else 0) =
      if IsProperAssignment H y then
        ∏ i : Fin m, (c - (D.bag i).card).descFactorial (k - (D.bag i).card) else 0 := by
    intro y
    by_cases hy : IsProperAssignment H y
    · simp only [hy, true_and, if_true]
      rw [← Finset.card_filter]
      have hset : (univ.filter fun z : (i : Fin m) → Fin (k - (D.bag i).card) → Fin c ↦
          ∀ i, Function.Injective (z i) ∧ ∀ t, z i t ∉ (D.bag i).image y) =
          Fintype.piFinset fun i : Fin m ↦
            (univ : Finset (Fin (k - (D.bag i).card) → Fin c)).filter
              fun w ↦ Function.Injective w ∧ ∀ t, w t ∉ (D.bag i).image y := by
        ext z
        simp [Fintype.mem_piFinset]
      rw [hset, Fintype.card_piFinset]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [card_injective_avoiding, card_image_of_isClique (D.bag_maximal i).1 hy]
    · simp [hy]
  simp_rw [hinner]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    properAssignmentCount]

/-! ### The unequal-bag chromatic factorization -/

/-- The factored polynomial `∏_i ∏_{s_i ≤ j < r_i} (X - j)`. -/
noncomputable def profilePoly : ℝ[X] :=
  ∏ i : Fin m, ∏ j ∈ Finset.Ico (s D i) (r D i), (X - C (j : ℝ))

lemma eval_profilePoly_natCast {c : ℕ} (hc : ∀ i, r D i ≤ c) :
    (profilePoly D).eval (c : ℝ) =
      ((∏ i : Fin m, (c - s D i).descFactorial (r D i - s D i) : ℕ) : ℝ) := by
  rw [profilePoly, eval_prod, Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [eval_prod, Finset.prod_Ico_eq_prod_range, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  have hjlt : j < r D i - s D i := Finset.mem_range.mp hj
  have hsr := s_le_r D i
  have hrc := hc i
  simp only [eval_sub, eval_X, eval_C]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_add]
  ring

/-- **The colouring count of `H` for `c ≥ k`.** -/
theorem properAssignmentCount_eq_profile (hk : ∀ i, (D.bag i).card ≤ k) {c : ℕ}
    (hc : k ≤ c) :
    properAssignmentCount H c = ∏ i : Fin m, (c - s D i).descFactorial (r D i - s D i) := by
  have hpure := (extDecomp D k hk).properAssignmentCount_eq_product c
  rw [properAssignmentCount_extGraph] at hpure
  simp_rw [extDecomp_sepCard] at hpure
  -- split each factor `(c - s)_{(k - s)} = (c - s)_{(r - s)} (c - r)_{(k - r)}`
  have hsplit : ∀ i : Fin m, (c - s D i).descFactorial (k - s D i) =
      (c - s D i).descFactorial (r D i - s D i) *
        (c - (D.bag i).card).descFactorial (k - (D.bag i).card) := by
    intro i
    have hsr := s_le_r D i
    have hrk := hk i
    have h := Nat.descFactorial_mul_descFactorial (n := c - s D i) (k := r D i - s D i)
      (m := k - s D i) (by unfold r at hsr ⊢; omega)
    rw [← h, mul_comm]
    congr 2
    · unfold r at hsr ⊢; omega
    · unfold r at hsr ⊢; omega
  simp_rw [hsplit] at hpure
  rw [Finset.prod_mul_distrib] at hpure
  have hpos : 0 < ∏ i : Fin m, (c - (D.bag i).card).descFactorial (k - (D.bag i).card) :=
    Finset.prod_pos fun i _ ↦ Nat.descFactorial_pos.mpr (by have := hk i; omega)
  exact Nat.eq_of_mul_eq_mul_right hpos hpure

/-- **The unequal-bag factorization**: `∏_i ∏_{s_i ≤ j < r_i} (X - j)` is the
chromatic polynomial of `H`. -/
theorem isChromaticPolynomial_profilePoly (hk : ∀ i, (D.bag i).card ≤ k) :
    IsChromaticPolynomial H (profilePoly D) := by
  obtain ⟨P, hP⟩ := exists_isChromaticPolynomial H
  have hPQ : P = profilePoly D := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinf : Set.Infinite ((fun c : ℕ ↦ ((k + c : ℕ) : ℝ)) '' Set.univ) :=
      (Set.infinite_univ).image fun a _ b _ h ↦ by
        have := Nat.cast_injective (R := ℝ) h
        omega
    apply hinf.mono
    rintro _ ⟨c, -, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [hP, eval_profilePoly_natCast D (fun i ↦ (hk i).trans (by omega)),
      properAssignmentCount_eq_profile D k hk (by omega)]
  rw [← hPQ]
  exact hP

/-- The clique number `k` (a bag of size `k`, all bags of size at most `k`) is the
chromatic number. -/
theorem isChromaticNumber_of_bags (hk : ∀ i, (D.bag i).card ≤ k) {i₀ : Fin m}
    (hi₀ : (D.bag i₀).card = k) : IsChromaticNumber H k where
  positive := by
    rw [properAssignmentCount_eq_profile D k hk le_rfl]
    refine Finset.prod_pos fun i _ ↦ Nat.descFactorial_pos.mpr ?_
    have := s_le_r D i
    have := hk i
    unfold r at *
    omega
  zero_below c hc :=
    properAssignmentCount_eq_zero_of_lt (D.bag_maximal i₀).1 (by rw [hi₀]; exact hc)

/-- `v(H) = ∑_i (r_i - s_i)`. -/
theorem card_eq_sum (hk : ∀ i, (D.bag i).card ≤ k) :
    Fintype.card V = ∑ i : Fin m, (r D i - s D i) := by
  have h := (isChromaticPolynomial_profilePoly D k hk).natDegree_le
  have hc := (isChromaticPolynomial_profilePoly D k hk).coeff_card
  have hmonic : (profilePoly D).Monic :=
    monic_prod_of_monic _ _ fun i _ ↦ monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _
  have hdeg : (profilePoly D).natDegree = ∑ i : Fin m, (r D i - s D i) := by
    rw [profilePoly, natDegree_prod_of_monic _ _ fun i _ ↦
      monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [natDegree_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
  -- a monic polynomial with coefficient one in degree `n` and degree `≤ n` has degree `n`
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt] at hc
    exact absurd hc zero_ne_one
  · rw [← heq, hdeg]

end Taeyoung.Paper.Profile
