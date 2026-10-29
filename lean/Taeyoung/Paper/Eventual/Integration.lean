import Taeyoung.Paper.Basic
import Taeyoung.Foundation.Link
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Weighted homomorphism integrals and leaf integration

The proof of Theorem 1.6 repeatedly integrates out a vertex of
degree one.  This file sets up the integrals that make this convenient: for a
family of graphons `κ e` indexed by the edges, an edge set `S`, and bounded
measurable vertex weights `φ v`,

`wInt κ S φ = ∫ ∏_{e ∈ S} κ_e(x_e) · ∏_v φ_v(x_v)`.

* `integral_comp_injective`: an integrand that only reads the coordinates in the
  image of an injection `φ : ι' → ι` integrates as over `ι'`;
* `integral_update`: integrating one coordinate out of an assignment integral;
* `wInt_leaf`: **leaf integration**.  If `ℓ` lies on exactly one edge `ℓu` of
  `S`, integrating `x_ℓ` replaces the weight at `u` by `φ_u · (κ_{ℓu} φ_ℓ)`;
* `wInt_empty`: with no edges the coordinates are independent.
-/

open MeasureTheory Finset

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Bounded measurable functions -/

/-- A bounded measurable real function on `Ω`: the vertex weights. -/
structure BddFun (Ω : Type*) [MeasurableSpace Ω] where
  toFun : Ω → ℝ
  measurable : Measurable toFun
  bound : ℝ
  abs_le : ∀ x, |toFun x| ≤ bound

instance : CoeFun (BddFun Ω) fun _ ↦ Ω → ℝ := ⟨BddFun.toFun⟩

namespace BddFun

/-- The constant function. -/
def const (c : ℝ) : BddFun Ω where
  toFun _ := c
  measurable := measurable_const
  bound := |c|
  abs_le _ := le_rfl

/-- The constant function `1`. -/
def one : BddFun Ω := const 1

@[simp] lemma const_apply (c : ℝ) (x : Ω) : (const c : BddFun Ω) x = c := rfl
@[simp] lemma one_apply (x : Ω) : (one : BddFun Ω) x = 1 := rfl

/-- Pointwise product. -/
def mul (f g : BddFun Ω) : BddFun Ω where
  toFun x := f x * g x
  measurable := f.measurable.mul g.measurable
  bound := f.bound * g.bound
  abs_le x := by
    rw [abs_mul]
    exact mul_le_mul (f.abs_le x) (g.abs_le x) (abs_nonneg _)
      ((abs_nonneg _).trans (f.abs_le x))

@[simp] lemma mul_apply (f g : BddFun Ω) (x : Ω) : (f.mul g) x = f x * g x := rfl

/-- A function built from a measurable bounded one. -/
def ofBound (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) : BddFun Ω :=
  ⟨f, hf, C, hC⟩

@[simp] lemma ofBound_apply (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C)
    (x : Ω) : (ofBound f hf C hC) x = f x := rfl

lemma integrable (f : BddFun Ω) : Integrable f μ :=
  (integrable_const (μ := μ) f.bound).mono' f.measurable.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact f.abs_le x)

end BddFun

/-- `(K f)(y) = ∫ K(y,z) f(z) dμ(z)`. -/
noncomputable def kernelApply (K : Graphon Ω μ) (f : Ω → ℝ) (y : Ω) : ℝ :=
  ∫ z, K y z * f z ∂μ

lemma measurable_kernelApply (K : Graphon Ω μ) {f : Ω → ℝ} (hf : Measurable f) :
    Measurable (kernelApply K f) := by
  have h : StronglyMeasurable (fun p : Ω × Ω ↦ K p.1 p.2 * f p.2) :=
    (K.measurable.mul (hf.comp measurable_snd)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := μ)).measurable

lemma integrable_kernel_mul (K : Graphon Ω μ) (f : BddFun Ω) (y : Ω) :
    Integrable (fun z ↦ K y z * f z) μ := by
  refine (integrable_const (μ := μ) f.bound).mono'
    ((K.measurable.comp (measurable_const.prodMk measurable_id)).mul
      f.measurable).aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |K y z| * |f z| ≤ 1 * f.bound := by
        refine mul_le_mul ?_ (f.abs_le z) (abs_nonneg _) zero_le_one
        rw [abs_of_nonneg (K.nonneg _ _)]
        exact K.le_one _ _
    _ = f.bound := one_mul _

lemma abs_kernelApply_le (K : Graphon Ω μ) (f : BddFun Ω) (y : Ω) :
    |kernelApply K f y| ≤ f.bound := by
  unfold kernelApply
  calc |∫ z, K y z * f z ∂μ| ≤ ∫ z, |K y z * f z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _z, f.bound ∂μ := by
        refine integral_mono (integrable_kernel_mul K f y).abs (integrable_const _) fun z ↦ ?_
        rw [abs_mul, abs_of_nonneg (K.nonneg _ _)]
        calc K y z * |f z| ≤ 1 * f.bound :=
              mul_le_mul (K.le_one _ _) (f.abs_le z) (abs_nonneg _) zero_le_one
          _ = f.bound := one_mul _
    _ = f.bound := by simp

/-- `K f` as a bounded measurable function. -/
noncomputable def BddFun.apply (K : Graphon Ω μ) (f : BddFun Ω) : BddFun Ω where
  toFun := kernelApply K f
  measurable := measurable_kernelApply K f.measurable
  bound := f.bound
  abs_le := abs_kernelApply_le K f

@[simp] lemma BddFun.apply_apply (K : Graphon Ω μ) (f : BddFun Ω) (y : Ω) :
    (BddFun.apply K f) y = ∫ z, K y z * f z ∂μ := rfl

/-! ### Two change-of-variables facts for assignment integrals -/

section Restriction

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

/-- Precomposition with an injection is measure-preserving between product
probability measures. -/
theorem measurePreserving_comp_injective {φ : ι' → ι} (hφ : Function.Injective φ) :
    MeasurePreserving (fun x : ι → Ω ↦ x ∘ φ) (assignmentMeasure ι μ)
      (assignmentMeasure ι' μ) := by
  have hmeas : Measurable fun x : ι → Ω ↦ x ∘ φ :=
    measurable_pi_lambda _ fun i ↦ measurable_pi_apply _
  refine ⟨hmeas, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  classical
  let t : ι → Set Ω := fun i ↦ if h : ∃ j, φ j = i then s h.choose else Set.univ
  have ht : ∀ j, t (φ j) = s j := by
    intro j
    have h : ∃ k, φ k = φ j := ⟨j, rfl⟩
    simp only [t, dif_pos h]
    rw [hφ h.choose_spec]
  have htu : ∀ i, i ∉ Set.range φ → t i = Set.univ := by
    intro i hi
    simp only [t]
    rw [dif_neg]
    rintro ⟨j, rfl⟩
    exact hi ⟨j, rfl⟩
  have hpre : (fun x : ι → Ω ↦ x ∘ φ) ⁻¹' Set.pi Set.univ s = Set.pi Set.univ t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply]
    constructor
    · intro hx i
      by_cases hi : i ∈ Set.range φ
      · obtain ⟨j, rfl⟩ := hi
        rw [ht]; exact hx j
      · rw [htu i hi]; exact Set.mem_univ _
    · intro hx j
      have := hx (φ j)
      rwa [ht] at this
  have hts : ∀ i, MeasurableSet (t i) := by
    intro i
    by_cases hi : i ∈ Set.range φ
    · obtain ⟨j, rfl⟩ := hi
      rw [ht]; exact hs j
    · rw [htu i hi]; exact MeasurableSet.univ
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre, assignmentMeasure,
    Measure.pi_pi]
  symm
  refine Fintype.prod_of_injective φ hφ _ _ (fun i hi ↦ ?_) (fun j ↦ by rw [ht])
  rw [htu i hi, measure_univ]

/-- **Unused coordinates drop out.**  An integrand reading only the coordinates
in the image of an injection integrates as over the smaller index type. -/
theorem integral_comp_injective {φ : ι' → ι} (hφ : Function.Injective φ)
    {g : (ι' → Ω) → ℝ} (hg : Measurable g) :
    ∫ x, g (x ∘ φ) ∂assignmentMeasure ι μ = ∫ y, g y ∂assignmentMeasure ι' μ := by
  have hmp := measurePreserving_comp_injective (μ := μ) hφ
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    hg.aestronglyMeasurable]

end Restriction

section Update

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Overwriting one coordinate with an independent sample preserves the
product measure. -/
theorem measurePreserving_update (v : V) :
    MeasurePreserving (fun p : (V → Ω) × Ω ↦ Function.update p.1 v p.2)
      ((assignmentMeasure V μ).prod μ) (assignmentMeasure V μ) := by
  have hmeas : Measurable fun p : (V → Ω) × Ω ↦ Function.update p.1 v p.2 :=
    measurable_update'
  refine ⟨hmeas, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have hpre : (fun p : (V → Ω) × Ω ↦ Function.update p.1 v p.2) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (Function.update s v Set.univ) ×ˢ s v := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun w ↦ ?_, by simpa using h v⟩
      by_cases hw : w = v
      · subst hw; simp
      · simpa [Function.update_of_ne hw] using h w
    · rintro ⟨h1, h2⟩ w
      by_cases hw : w = v
      · subst hw; simpa using h2
      · simpa [Function.update_of_ne hw] using h1 w
  have hsu : ∀ w, MeasurableSet (Function.update s v Set.univ w) := by
    intro w
    by_cases hw : w = v
    · subst hw; simp
    · rw [Function.update_of_ne hw]; exact hs w
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    assignmentMeasure, Measure.pi_pi]
  have hfun : (fun w ↦ μ (Function.update s v Set.univ w)) =
      Function.update (fun w ↦ μ (s w)) v 1 := by
    funext w
    by_cases hw : w = v
    · subst hw; simp
    · rw [Function.update_of_ne hw, Function.update_of_ne hw]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ v), one_mul,
    ← Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ v)]

/-- **Integrating out one coordinate.** -/
theorem integral_update (v : V) {f : (V → Ω) → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    ∫ x, f x ∂assignmentMeasure V μ =
      ∫ x, (∫ y, f (Function.update x v y) ∂μ) ∂assignmentMeasure V μ := by
  have hmp := measurePreserving_update (μ := μ) v
  have hcomp : Measurable fun p : (V → Ω) × Ω ↦ f (Function.update p.1 v p.2) :=
    hf.comp hmp.measurable
  conv_lhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable hf.aestronglyMeasurable]
  refine integral_prod (μ := assignmentMeasure V μ) (ν := μ)
    (fun p : (V → Ω) × Ω ↦ f (Function.update p.1 v p.2)) ?_
  refine (integrable_const C).mono' hcomp.aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
  rw [Real.norm_eq_abs]; exact hC _

end Update

/-! ### Weighted edge integrals -/

section Weighted

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `∏_{e ∈ S} κ_e(x_e)`. -/
def edgeProd (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V)) (x : V → Ω) : ℝ :=
  ∏ e ∈ S, edgeValue (κ e) x e

/-- `∏_v φ_v(x_v)`. -/
def vertexProd (φ : V → BddFun Ω) (x : V → Ω) : ℝ := ∏ v, φ v (x v)

/-- The weighted edge integral `∫ ∏_{e ∈ S} κ_e(x_e) ∏_v φ_v(x_v)`. -/
noncomputable def wInt (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V))
    (φ : V → BddFun Ω) : ℝ :=
  ∫ x, edgeProd κ S x * vertexProd φ x ∂assignmentMeasure V μ

lemma measurable_edgeProd (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V)) :
    Measurable (edgeProd κ S) :=
  Finset.measurable_fun_prod _ fun e _ ↦ measurable_edgeValue (κ e) e

lemma measurable_vertexProd (φ : V → BddFun Ω) : Measurable (vertexProd φ) :=
  Finset.measurable_fun_prod _ fun v _ ↦ (φ v).measurable.comp (measurable_pi_apply v)

lemma edgeProd_nonneg (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V)) (x : V → Ω) :
    0 ≤ edgeProd κ S x :=
  Finset.prod_nonneg fun e _ ↦ edgeValue_nonneg _ x e

lemma edgeProd_le_one (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V)) (x : V → Ω) :
    edgeProd κ S x ≤ 1 :=
  Finset.prod_le_one (fun e _ ↦ edgeValue_nonneg _ x e) fun e _ ↦ edgeValue_le_one _ x e

lemma abs_vertexProd_le (φ : V → BddFun Ω) (x : V → Ω) :
    |vertexProd φ x| ≤ ∏ v, (φ v).bound := by
  unfold vertexProd
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun v _ ↦ abs_nonneg _) fun v _ ↦ (φ v).abs_le _

lemma abs_integrand_le (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V))
    (φ : V → BddFun Ω) (x : V → Ω) :
    |edgeProd κ S x * vertexProd φ x| ≤ ∏ v, (φ v).bound := by
  rw [abs_mul, abs_of_nonneg (edgeProd_nonneg κ S x)]
  calc edgeProd κ S x * |vertexProd φ x| ≤ 1 * ∏ v, (φ v).bound :=
        mul_le_mul (edgeProd_le_one κ S x) (abs_vertexProd_le φ x) (abs_nonneg _)
          zero_le_one
    _ = _ := one_mul _

lemma measurable_integrand (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V))
    (φ : V → BddFun Ω) : Measurable fun x ↦ edgeProd κ S x * vertexProd φ x :=
  (measurable_edgeProd κ S).mul (measurable_vertexProd φ)

lemma integrable_integrand (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V))
    (φ : V → BddFun Ω) :
    Integrable (fun x ↦ edgeProd κ S x * vertexProd φ x) (assignmentMeasure V μ) :=
  integrable_of_bounded (measurable_integrand κ S φ) (abs_integrand_le κ S φ)

/-- Changing the coordinate `v` does not change an edge value off `v`. -/
lemma edgeValue_update_of_notMem (W : Graphon Ω μ) (x : V → Ω) {v : V} {e : Sym2 V}
    (hv : v ∉ e) (y : Ω) : edgeValue W (Function.update x v y) e = edgeValue W x e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    have ha : a ≠ v := fun h ↦ hv (h ▸ Sym2.mem_mk_left a b)
    have hb : b ≠ v := fun h ↦ hv (h ▸ Sym2.mem_mk_right a b)
    rw [edgeValue_mk, edgeValue_mk, Function.update_of_ne ha, Function.update_of_ne hb]

lemma edgeProd_update_of_notMem (κ : Sym2 V → Graphon Ω μ) {S : Finset (Sym2 V)}
    (x : V → Ω) {v : V} (hv : ∀ e ∈ S, v ∉ e) (y : Ω) :
    edgeProd κ S (Function.update x v y) = edgeProd κ S x :=
  Finset.prod_congr rfl fun e he ↦ edgeValue_update_of_notMem _ x (hv e he) y

/-- `∏_v ψ_v = ψ_ℓ ∏_{v ≠ ℓ} ψ_v`. -/
lemma prod_univ_eq_mul_erase (ψ : V → ℝ) (ℓ : V) :
    ∏ v, ψ v = ψ ℓ * ∏ v ∈ univ.erase ℓ, ψ v :=
  (Finset.mul_prod_erase univ ψ (mem_univ ℓ)).symm

/-- **Leaf integration.**  If `ℓ` lies on exactly one edge `ℓu` of `S`, then
integrating `x_ℓ` turns that edge and the weight at `ℓ` into the factor
`(κ_{ℓu} φ_ℓ)(x_u)` at `u`. -/
theorem wInt_leaf (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V)) (φ : V → BddFun Ω)
    {ℓ u : V} (hℓu : ℓ ≠ u) (he : s(ℓ, u) ∈ S) (honly : ∀ e ∈ S, ℓ ∈ e → e = s(ℓ, u)) :
    wInt κ S φ = wInt κ (S.erase s(ℓ, u))
      (Function.update (Function.update φ ℓ BddFun.one) u
        ((φ u).mul (BddFun.apply (κ s(ℓ, u)) (φ ℓ)))) := by
  set e := s(ℓ, u) with he_def
  set φ' := Function.update (Function.update φ ℓ BddFun.one) u
    ((φ u).mul (BddFun.apply (κ e) (φ ℓ))) with hφ'
  have hnot : ∀ f ∈ S.erase e, ℓ ∉ f := by
    intro f hf hℓf
    exact (Finset.mem_erase.mp hf).1 (honly f (Finset.mem_erase.mp hf).2 hℓf)
  unfold wInt
  rw [integral_update ℓ (measurable_integrand κ S φ) (abs_integrand_le κ S φ)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only []
  -- the integrand after updating the coordinate `ℓ`
  have hpt : ∀ y, edgeProd κ S (Function.update x ℓ y) * vertexProd φ (Function.update x ℓ y) =
      (edgeProd κ (S.erase e) x * ∏ v ∈ univ.erase ℓ, φ v (x v)) *
        ((κ e) (x u) y * φ ℓ y) := by
    intro y
    have h1 : edgeProd κ S (Function.update x ℓ y) =
        edgeValue (κ e) (Function.update x ℓ y) e *
          edgeProd κ (S.erase e) (Function.update x ℓ y) :=
      (Finset.mul_prod_erase S _ he).symm
    have h2 : edgeValue (κ e) (Function.update x ℓ y) e = (κ e) (x u) y := by
      rw [he_def, edgeValue_mk, Function.update_self, Function.update_of_ne hℓu.symm,
        (κ _).symm]
    have h3 : vertexProd φ (Function.update x ℓ y) =
        φ ℓ y * ∏ v ∈ univ.erase ℓ, φ v (x v) := by
      unfold vertexProd
      rw [prod_univ_eq_mul_erase _ ℓ, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun v hv ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
    rw [h1, h2, h3, edgeProd_update_of_notMem κ x hnot y]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  -- the right-hand integrand
  have hrhs : vertexProd φ' x =
      (∏ v ∈ univ.erase ℓ, φ v (x v)) * ∫ z, (κ e) (x u) z * φ ℓ z ∂μ := by
    unfold vertexProd
    rw [prod_univ_eq_mul_erase _ ℓ]
    have hℓ : φ' ℓ (x ℓ) = 1 := by
      rw [hφ', Function.update_of_ne hℓu, Function.update_self]; rfl
    rw [hℓ, one_mul]
    have hu : u ∈ univ.erase ℓ := Finset.mem_erase.mpr ⟨hℓu.symm, mem_univ u⟩
    rw [← Finset.mul_prod_erase _ _ hu, ← Finset.mul_prod_erase _ (fun v ↦ φ v (x v)) hu]
    have hφu : φ' u (x u) = φ u (x u) * ∫ z, (κ e) (x u) z * φ ℓ z ∂μ := by
      rw [hφ', Function.update_self]; rfl
    rw [hφu]
    have hrest : ∏ v ∈ (univ.erase ℓ).erase u, φ' v (x v) =
        ∏ v ∈ (univ.erase ℓ).erase u, φ v (x v) := by
      refine Finset.prod_congr rfl fun v hv ↦ ?_
      have hvu : v ≠ u := Finset.ne_of_mem_erase hv
      have hvℓ : v ≠ ℓ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hv)
      rw [hφ', Function.update_of_ne hvu, Function.update_of_ne hvℓ]
    rw [hrest]
    ring
  rw [hrhs]
  ring

/-- With no edges the coordinates are independent. -/
theorem wInt_empty (κ : Sym2 V → Graphon Ω μ) (φ : V → BddFun Ω) :
    wInt κ ∅ φ = ∏ v, ∫ y, φ v y ∂μ := by
  unfold wInt edgeProd vertexProd
  simp only [Finset.prod_empty, one_mul]
  exact integral_fintype_prod_eq_prod (fun v y ↦ φ v y)

/-- Weighted integrals depend only on the edge kernels used on `S`. -/
lemma wInt_congr_kernel {κ κ' : Sym2 V → Graphon Ω μ} {S : Finset (Sym2 V)}
    (h : ∀ e ∈ S, κ e = κ' e) (φ : V → BddFun Ω) : wInt κ S φ = wInt κ' S φ := by
  unfold wInt edgeProd
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only []
  rw [Finset.prod_congr rfl fun e he ↦ by rw [h e he]]

/-- Weighted integrals depend only on the values of the weights. -/
lemma wInt_congr_weight (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V))
    {φ ψ : V → BddFun Ω} (h : ∀ v y, φ v y = ψ v y) : wInt κ S φ = wInt κ S ψ := by
  unfold wInt vertexProd
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [h]

/-- Monotonicity in the integrand, for nonnegative weights. -/
lemma wInt_mono_of_le {κ κ' : Sym2 V → Graphon Ω μ} {S S' : Finset (Sym2 V)}
    {φ ψ : V → BddFun Ω}
    (h : ∀ x, edgeProd κ S x * vertexProd φ x ≤ edgeProd κ' S' x * vertexProd ψ x) :
    wInt κ S φ ≤ wInt κ' S' ψ :=
  integral_mono (integrable_integrand κ S φ) (integrable_integrand κ' S' ψ) h

/-- Nonnegative weights give nonnegative integrals. -/
lemma wInt_nonneg (κ : Sym2 V → Graphon Ω μ) (S : Finset (Sym2 V)) {φ : V → BddFun Ω}
    (hφ : ∀ v y, 0 ≤ φ v y) : 0 ≤ wInt κ S φ :=
  integral_nonneg fun x ↦ mul_nonneg (edgeProd_nonneg κ S x)
    (Finset.prod_nonneg fun v _ ↦ hφ v _)

end Weighted

end Taeyoung.Paper.Eventual
