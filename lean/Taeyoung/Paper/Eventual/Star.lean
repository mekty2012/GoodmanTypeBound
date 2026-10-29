import Taeyoung.Paper.Eventual.Forests

/-!
# Stars

Integrating all leaves of a star at once: if `v ∉ L`, the edges `vw` (`w ∈ L`)
carry kernels `κ`, and the vertices carry weights `φ`, then

`wInt κ {vw : w ∈ L} φ = (∫ φ_v ∏_{w ∈ L} (κ_{vw} φ_w)) · ∏_{u ≠ v, u ∉ L} ∫ φ_u`.
-/

open MeasureTheory Finset

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of the star with centre `v` and leaves `L`. -/
def starEdges (v : V) (L : Finset V) : Finset (Sym2 V) := L.image fun w ↦ s(v, w)

lemma mem_starEdges {v : V} {L : Finset V} {e : Sym2 V} :
    e ∈ starEdges v L ↔ ∃ w ∈ L, s(v, w) = e := by
  unfold starEdges; rw [Finset.mem_image]

/-- **Star integration.** -/
theorem wInt_star (κ : Sym2 V → Graphon Ω μ) (v : V) :
    ∀ (L : Finset V), v ∉ L → ∀ φ : V → BddFun Ω,
      wInt κ (starEdges v L) φ =
        (∫ y, φ v y * ∏ w ∈ L, kernelApply (κ s(v, w)) (φ w) y ∂μ) *
          ∏ u ∈ (univ.erase v) \ L, ∫ y, φ u y ∂μ := by
  intro L
  induction L using Finset.induction_on with
  | empty =>
    intro _ φ
    have h : starEdges v (∅ : Finset V) = ∅ := by simp [starEdges]
    rw [h, wInt_empty, Finset.sdiff_empty, ← Finset.mul_prod_erase univ _ (mem_univ v)]
    simp
  | @insert w L hwL ih =>
    intro hv φ
    have hwv : w ≠ v := fun h ↦ hv (h ▸ Finset.mem_insert_self w L)
    have hvL : v ∉ L := fun h ↦ hv (Finset.mem_insert_of_mem h)
    have hS : starEdges v (insert w L) = insert s(w, v) (starEdges v L) := by
      unfold starEdges; rw [Finset.image_insert, Sym2.eq_swap]
    have hnot : s(w, v) ∉ starEdges v L := by
      intro h
      obtain ⟨w', hw', he⟩ := mem_starEdges.mp h
      rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hwv h1.symm
      · exact hwL (h2 ▸ hw')
    have honly : ∀ e ∈ insert s(w, v) (starEdges v L), w ∈ e → e = s(w, v) := by
      intro e he hwe
      rcases Finset.mem_insert.mp he with h | h
      · exact h
      · obtain ⟨w', hw', rfl⟩ := mem_starEdges.mp h
        rcases Sym2.mem_iff.mp hwe with h1 | h1
        · exact absurd h1 hwv
        · exact absurd (h1 ▸ hw') hwL
    rw [hS, wInt_leaf κ _ φ hwv (Finset.mem_insert_self _ _) honly,
      Finset.erase_insert hnot, ih hvL]
    set φ' := Function.update (Function.update φ w BddFun.one) v
      ((φ v).mul (BddFun.apply (κ s(w, v)) (φ w)))
    have hv' : ∀ y, φ' v y = φ v y * kernelApply (κ s(v, w)) (φ w) y := by
      intro y
      simp only [φ', Function.update_self, BddFun.mul_apply, BddFun.apply_apply]
      rw [Sym2.eq_swap]; rfl
    have hL' : ∀ w' ∈ L, φ' w' = φ w' := by
      intro w' hw'
      have h1 : w' ≠ v := fun h ↦ hvL (h ▸ hw')
      have h2 : w' ≠ w := fun h ↦ hwL (h ▸ hw')
      simp only [φ', Function.update_of_ne h1, Function.update_of_ne h2]
    have hrest : ∀ u ∈ (univ.erase v) \ insert w L, φ' u = φ u := by
      intro u hu
      have hu' := Finset.mem_sdiff.mp hu
      have h1 : u ≠ v := Finset.ne_of_mem_erase hu'.1
      have h2 : u ≠ w := fun h ↦ hu'.2 (h ▸ Finset.mem_insert_self w L)
      simp only [φ', Function.update_of_ne h1, Function.update_of_ne h2]
    have hset : (univ.erase v) \ L = insert w ((univ.erase v) \ insert w L) := by
      ext u
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases huw : u = w
        · exact Or.inl huw
        · exact Or.inr ⟨h1, fun h ↦ h.elim huw h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨hwv, hwL⟩
        · exact ⟨h1, fun h ↦ h2 (Or.inr h)⟩
    have hw_notin : w ∉ (univ.erase v) \ insert w L := by simp
    rw [hset, Finset.prod_insert hw_notin]
    have hw1 : ∫ y, φ' w y ∂μ = 1 := by
      simp [φ', Function.update_of_ne hwv, BddFun.one]
    rw [hw1, one_mul, Finset.prod_congr rfl fun u hu ↦ by rw [hrest u hu]]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    simp only []
    rw [hv', Finset.prod_congr rfl fun w' hw' ↦ by rw [hL' w' hw'], Finset.prod_insert hwL]
    ring

end Taeyoung.Paper.Eventual
