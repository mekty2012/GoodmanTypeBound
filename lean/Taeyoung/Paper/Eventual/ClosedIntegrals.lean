import Taeyoung.Paper.Eventual.Kernels
import Taeyoung.Paper.Eventual.Closed
import Taeyoung.Paper.Eventual.Expansion

/-!
# Integrals over closed forests (`paper.pdf`, proofs of Lemma 4.5 and
Proposition 4.12)

Let `e ∈ B(F)` with closing path `P ⊆ F` of length `s - 1`.

* `wInt_closingPath`: `∫ ∏_{f ∈ P} U_f (1 - U_e) = Q_s`: relabel the path to
  `Fin s` and integrate out its interior;
* `ClosedBounds.lean` uses this for the leaf-integration estimate
  `I_F(U) ≤ Δ^{|F| - |P|} Q_s` (`intervalInt_le_closing`: drop the other closed
  edges and integrate the leaves of `F` hanging off the path) and, when
  `|F| = g - 1`, `I_F(U) = Q_g` (`intervalInt_leading`).
-/

open MeasureTheory Finset SimpleGraph

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The closing-path integral on `Fin s` -/

lemma list_prod_map_range {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∀ m : ℕ, ((List.range m).map f).prod = ∏ i : Fin m, f i
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, list_prod_map_range f m,
      Fin.prod_univ_castSucc]
    simp

lemma prod_path_eq (U : Graphon Ω μ) (n : ℕ) (y : Fin (n + 2) → Ω) :
    ∏ i : Fin (n + 1), U (y i.castSucc) (y i.succ) =
      Paper.pathWeight U n (y 0) (y (Fin.last (n + 1))) (Fin.tail (Fin.init y)) := by
  rw [Fin.prod_univ_castSucc]
  have := Paper.prod_path_eq_pathWeight U n (Fin.init y) (y (Fin.last (n + 1)))
  simp only [Fin.init] at this
  convert this using 2
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Fin.succ_castSucc]
  · rw [Fin.succ_last]
  · simp

/-- **The closing-path integral**: `∫_{Fin (n+2)} ∏_{path} U · (1 - U_{ends}) = Q_{n+2}`. -/
theorem integral_closingPath (U : Graphon Ω μ) (n : ℕ) :
    ∫ y, (∏ i : Fin (n + 1), U (y i.castSucc) (y i.succ)) *
        (1 - U (y 0) (y (Fin.last (n + 1)))) ∂assignmentMeasure (Fin (n + 2)) μ =
      Qs U (n + 2) := by
  simp_rw [prod_path_eq]
  set G : (Fin (n + 2) → Ω) → ℝ := fun y ↦ Paper.pathWeight U n (y 0) (y (Fin.last (n + 1)))
    (Fin.tail (Fin.init y)) * (1 - U (y 0) (y (Fin.last (n + 1)))) with hG
  have hGb : ∀ y, |G y| ≤ 1 := by
    intro y
    have h1 := Paper.pathWeight_nonneg U n (y 0) (y (Fin.last (n + 1))) (Fin.tail (Fin.init y))
    have h2 := Paper.pathWeight_le_one U n (y 0) (y (Fin.last (n + 1))) (Fin.tail (Fin.init y))
    have h3 := U.nonneg (y 0) (y (Fin.last (n + 1)))
    have h4 := U.le_one (y 0) (y (Fin.last (n + 1)))
    rw [hG, abs_le]
    constructor <;> nlinarith
  have hmeas_tri : ∀ {k : ℕ}, Measurable fun y : Fin (k + 2) → Ω ↦
      (y 0, y (Fin.last (k + 1)), Fin.tail (Fin.init y)) := by
    intro k
    refine (measurable_pi_apply 0).prodMk ((measurable_pi_apply _).prodMk ?_)
    exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply _
  have hGm : Measurable G := by
    rw [hG]
    exact ((Paper.measurable_pathWeight U n).comp hmeas_tri).mul
      (measurable_const.sub (U.measurable.comp
        (((measurable_pi_apply 0).prodMk (measurable_pi_apply _)) :
          Measurable fun y : Fin (n + 2) → Ω ↦ (y 0, y (Fin.last (n + 1))))))
  rw [integral_assignmentMeasure_last G hGm hGb]
  -- `y = snoc z b`
  have hsnoc : ∀ (z : Fin (n + 1) → Ω) (b : Ω), G (Fin.snoc z b) =
      Paper.pathWeight U n (z 0) b (Fin.tail z) * (1 - U (z 0) b) := by
    intro z b
    rw [hG]
    simp only [Fin.snoc_last, Fin.init_snoc]
    have h0 : (Fin.snoc z b : Fin (n + 2) → Ω) 0 = z 0 := by
      have := Fin.snoc_castSucc (α := fun _ ↦ Ω) (p := z) (x := b) (i := 0)
      simpa using this
    rw [h0]
  simp_rw [hsnoc]
  -- peel the first coordinate
  have hinner : ∀ b, ∫ z, Paper.pathWeight U n (z 0) b (Fin.tail z) * (1 - U (z 0) b)
      ∂assignmentMeasure (Fin (n + 1)) μ = ∫ a, pk U n a b * (1 - U a b) ∂μ := by
    intro b
    have hm : Measurable fun z : Fin (n + 1) → Ω ↦
        Paper.pathWeight U n (z 0) b (Fin.tail z) * (1 - U (z 0) b) := by
      have h1 : Measurable fun z : Fin (n + 1) → Ω ↦ (z 0, b, Fin.tail z) :=
        (measurable_pi_apply 0).prodMk (measurable_const.prodMk
          (measurable_pi_lambda _ fun i ↦ measurable_pi_apply _))
      exact ((Paper.measurable_pathWeight U n).comp h1).mul
        (measurable_const.sub (U.measurable.comp (((measurable_pi_apply 0).prodMk
          measurable_const) : Measurable fun z : Fin (n + 1) → Ω ↦ (z 0, b))))
    rw [integral_assignmentMeasure_succ _ hm (C := 1) fun z ↦ by
      have := hGb (Fin.snoc z b)
      rwa [hsnoc] at this]
    refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [integral_mul_const, Paper.integral_pathWeight]
  simp_rw [hinner]
  have hb := (bdd2_pk U n).mul (bdd2_one_sub U)
  rw [Qs, show n + 2 - 2 = n by omega, dint_swap hb]

/-! ### Relabelling a closing path -/

variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- The integrand of a closing path, read along the path. -/
lemma prod_edgeSet'_eq {F : Finset (Sym2 V)} {e : Sym2 V} (cp : ClosingPath H F e)
    (U : Graphon Ω μ) (x : V → Ω) :
    ∏ f ∈ cp.edgeSet', edgeValue U x f =
      ∏ i ∈ Finset.range cp.p.length, U (x (cp.p.getVert i)) (x (cp.p.getVert (i + 1))) := by
  unfold ClosingPath.edgeSet'
  rw [List.prod_toFinset _ cp.isPath.isTrail.edges_nodup, edges_eq_map_getVert, List.map_map,
    list_prod_map_range, Fin.prod_univ_eq_prod_range
      (fun i ↦ (edgeValue U x ∘ fun i ↦ s(cp.p.getVert i, cp.p.getVert (i + 1))) i)]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp

/-- **The closing-path integral, on `V`.** -/
theorem wInt_closingPath {F : Finset (Sym2 V)} {e : Sym2 V} (cp : ClosingPath H F e)
    (U : Graphon Ω μ) {n : ℕ} (hlen : cp.p.length = n + 1) :
    wInt (closedKernel U {e}) (cp.edgeSet' ∪ {e}) (fun _ ↦ BddFun.one) = Qs U (n + 2) := by
  have hdisj : Disjoint cp.edgeSet' {e} := Finset.disjoint_singleton_right.mpr cp.e_notMem_edgeSet'
  set φ : Fin (n + 2) → V := fun i ↦ cp.p.getVert i with hφ
  have hφinj : Function.Injective φ := by
    intro i j hij
    have := cp.isPath.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hij
    exact Fin.ext this
  set g : (Fin (n + 2) → Ω) → ℝ := fun y ↦ (∏ i : Fin (n + 1), U (y i.castSucc) (y i.succ)) *
    (1 - U (y 0) (y (Fin.last (n + 1)))) with hg
  have hpt : ∀ x : V → Ω, edgeProd (closedKernel U {e}) (cp.edgeSet' ∪ {e}) x *
      vertexProd (fun _ ↦ BddFun.one) x = g (x ∘ φ) := by
    intro x
    rw [edgeProd_closedKernel U hdisj, prod_edgeSet'_eq cp U x]
    have hv : vertexProd (fun _ : V ↦ (BddFun.one : BddFun Ω)) x = 1 := by
      simp [vertexProd, BddFun.one]
    rw [hv, mul_one, hg]
    simp only [Finset.prod_singleton, Function.comp_apply]
    have hprod : ∏ i ∈ Finset.range cp.p.length,
        U (x (cp.p.getVert i)) (x (cp.p.getVert (i + 1))) =
        ∏ i : Fin (n + 1), U (x (φ i.castSucc)) (x (φ i.succ)) := by
      rw [hlen, ← Fin.prod_univ_eq_prod_range (fun i ↦ U (x (cp.p.getVert i))
        (x (cp.p.getVert (i + 1))))]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      simp [hφ]
    rw [hprod]
    congr 1
    have he : edgeValue U x e = U (x (φ 0)) (x (φ (Fin.last (n + 1)))) := by
      rw [cp.e_eq, edgeValue_mk]
      simp only [hφ, Fin.val_zero, Walk.getVert_zero, Fin.val_last]
      rw [← hlen, Walk.getVert_length]
    rw [he]
  unfold wInt
  simp_rw [hpt]
  have hgm : Measurable g := by
    rw [hg]
    refine (Finset.measurable_fun_prod _ fun i _ ↦ ?_).mul
      (measurable_const.sub (U.measurable.comp
        (((measurable_pi_apply 0).prodMk (measurable_pi_apply _)) :
          Measurable fun y : Fin (n + 2) → Ω ↦ (y 0, y (Fin.last (n + 1))))))
    exact U.measurable.comp (((measurable_pi_apply _).prodMk (measurable_pi_apply _)) :
      Measurable fun y : Fin (n + 2) → Ω ↦ (y i.castSucc, y i.succ))
  rw [integral_comp_injective hφinj hgm]
  exact integral_closingPath U n

end Taeyoung.Paper.Eventual
