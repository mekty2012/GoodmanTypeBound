import Taeyoung.Paper.Eventual.ClosedSum
import Taeyoung.Paper.Eventual.EvenGirth

/-!
# Small forests (`paper.pdf`, proof of Proposition 4.12)

* `forestDens_two`: a two-edge forest has density `M_2 = q² + X` if its edges
  share a vertex and `q²` otherwise; in particular `t(F,U) ≥ q²`;
* `sum_forest_error_le`: `∑_{F ⊆ E, |F| ≥ 3} C(|F|,2) Δ^{|F|-2} ≤ m³ Δ` when `mΔ ≤ 1/2`;
* `geom_le`: `∑_{j < N} x^{j+1} ≤ 2x` for `0 ≤ x ≤ 1/2`.
-/

open MeasureTheory Finset SimpleGraph

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Elementary sums -/

lemma geom_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (N : ℕ) :
    ∑ j ∈ Finset.range N, x ^ (j + 1) ≤ 2 * x := by
  have key : ∀ N, ∑ j ∈ Finset.range N, x ^ (j + 1) ≤ 2 * x - 2 * x ^ (N + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have h1 : 2 * x ^ (N + 1 + 1) ≤ x ^ (N + 1) := by
        rw [pow_succ]
        have := pow_nonneg hx0 (N + 1)
        nlinarith
      linarith
  have := key N
  have := pow_nonneg hx0 (N + 1)
  linarith

lemma choose_mul_choose_two_le (m r : ℕ) (hr : 2 ≤ r) :
    2 * (m.choose r * r.choose 2) ≤ m ^ r := by
  have h1 : 2 * r.choose 2 ≤ r.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := r) (k := 2) hr
    have h2 : 1 ≤ (r - 2).factorial := Nat.factorial_pos _
    rw [Nat.factorial_two] at this
    nlinarith
  have h3 : m.choose r * r.factorial ≤ m ^ r := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow m r
  calc 2 * (m.choose r * r.choose 2) = m.choose r * (2 * r.choose 2) := by ring
    _ ≤ m.choose r * r.factorial := Nat.mul_le_mul_left _ h1
    _ ≤ m ^ r := h3

/-- **(4.28)**, the coefficient of `X`:
`∑_{F ⊆ E, |F| ≥ 3} C(|F|,2) Δ^{|F|-2} ≤ m³ Δ` when `mΔ ≤ 1/2`; this is sharper
than the paper's final bound `2m³Δ`. -/
theorem sum_forest_error_le (E : Finset (Sym2 V)) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hmΔ : (E.card : ℝ) * Δ ≤ 1 / 2) :
    ∑ F ∈ E.powerset, (if 3 ≤ F.card then (F.card.choose 2 : ℝ) * Δ ^ (F.card - 2) else 0) ≤
      (E.card : ℝ) ^ 3 * Δ := by
  set m := E.card
  rw [Finset.sum_powerset_apply_card (fun r ↦ if 3 ≤ r then (r.choose 2 : ℝ) * Δ ^ (r - 2)
    else 0)]
  have hterm : ∀ r ∈ Finset.range (m + 1), (m.choose r) • (if 3 ≤ r then (r.choose 2 : ℝ) *
      Δ ^ (r - 2) else 0) ≤ if 3 ≤ r then (m : ℝ) ^ 2 / 2 * ((m : ℝ) * Δ) ^ (r - 2) else 0 := by
    intro r _
    split_ifs with h3
    · rw [nsmul_eq_mul]
      have hc := choose_mul_choose_two_le m r (by omega)
      have hc' : 2 * ((m.choose r : ℝ) * (r.choose 2 : ℝ)) ≤ (m : ℝ) ^ r := by exact_mod_cast hc
      have hmr : (m : ℝ) ^ r = (m : ℝ) ^ 2 * (m : ℝ) ^ (r - 2) := by
        rw [← pow_add]; congr 1; omega
      have hΔr := pow_nonneg hΔ0 (r - 2)
      rw [mul_pow]
      calc (m.choose r : ℝ) * ((r.choose 2 : ℝ) * Δ ^ (r - 2)) =
          ((m.choose r : ℝ) * (r.choose 2 : ℝ)) * Δ ^ (r - 2) := by ring
        _ ≤ ((m : ℝ) ^ r / 2) * Δ ^ (r - 2) := by
            apply mul_le_mul_of_nonneg_right _ hΔr; linarith
        _ = (m : ℝ) ^ 2 / 2 * ((m : ℝ) ^ (r - 2) * Δ ^ (r - 2)) := by rw [hmr]; ring
    · simp
  refine (Finset.sum_le_sum hterm).trans ?_
  -- reindex `r = j + 3`
  have hsplit : ∑ r ∈ Finset.range (m + 1), (if 3 ≤ r then (m : ℝ) ^ 2 / 2 * ((m : ℝ) * Δ) ^ (r - 2)
      else 0) = ∑ j ∈ Finset.range (m + 1 - 3), (m : ℝ) ^ 2 / 2 * ((m : ℝ) * Δ) ^ (j + 1) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (min 3 (m + 1)))
      (min_le_right 3 (m + 1))]
    have h1 : ∑ r ∈ Finset.Ico 0 (min 3 (m + 1)), (if 3 ≤ r then (m : ℝ) ^ 2 / 2 *
        ((m : ℝ) * Δ) ^ (r - 2) else 0) = 0 :=
      Finset.sum_eq_zero fun r hr ↦ by
        rw [if_neg]; have := (Finset.mem_Ico.mp hr).2; omega
    rw [h1, zero_add, Finset.sum_Ico_eq_sum_range]
    by_cases hm : 3 ≤ m + 1
    · rw [min_eq_left hm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [if_pos (by omega)]; congr 2; omega
    · have : m + 1 - min 3 (m + 1) = 0 := by omega
      rw [this, show m + 1 - 3 = 0 by omega]
      simp only [Finset.sum_range_zero]
  rw [hsplit, ← Finset.mul_sum]
  have hg := geom_le (mul_nonneg (Nat.cast_nonneg m) hΔ0) hmΔ (m + 1 - 3)
  have hm2 : 0 ≤ (m : ℝ) ^ 2 / 2 := by positivity
  calc (m : ℝ) ^ 2 / 2 * ∑ j ∈ Finset.range (m + 1 - 3), ((m : ℝ) * Δ) ^ (j + 1)
      ≤ (m : ℝ) ^ 2 / 2 * (2 * ((m : ℝ) * Δ)) := mul_le_mul_of_nonneg_left hg hm2
    _ = (m : ℝ) ^ 3 * Δ := by ring

/-! ### Two-edge forests -/

lemma Mom_two_eq (U : Graphon Ω μ) : Mom U 2 = meanDeg U ^ 2 + degVar U := by
  unfold Mom degVar
  have hd := (isBdd_degree U).integrable (μ := μ)
  have hd2 := (isBdd_degree U).sq.integrable (μ := μ)
  have : (fun x ↦ (degree U x - meanDeg U) ^ 2) =
      fun x ↦ degree U x ^ 2 + (-(2 * meanDeg U)) * degree U x + meanDeg U ^ 2 * 1 := by
    funext x; ring
  rw [this, integral_lin3 hd2 hd (integrable_const 1)]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  unfold meanDeg
  ring

/-- **Two-edge forests**: `t(F,U) = q²` or `M_2 = q² + X`. -/
theorem forestDens_two (U : Graphon Ω μ) {F : Finset (Sym2 V)} (hnd : ∀ f ∈ F, ¬ f.IsDiag)
    (hcard : F.card = 2) :
    (∃ v, ∀ f ∈ F, v ∈ f) ∧ forestDens U F = Mom U 2 ∨
      ¬ (∃ v, ∀ f ∈ F, v ∈ f) ∧ forestDens U F = meanDeg U ^ 2 := by
  obtain ⟨f₁, f₂, hne, rfl⟩ := Finset.card_eq_two.mp hcard
  have hnd₁ := hnd f₁ (by simp)
  have hnd₂ := hnd f₂ (by simp)
  -- an end of `f₁` off `f₂`
  obtain ⟨ℓ, u, hℓu, rfl, hℓ⟩ : ∃ ℓ u, ℓ ≠ u ∧ f₁ = s(ℓ, u) ∧ ℓ ∉ f₂ := by
    induction f₁ using Sym2.inductionOn with
    | _ a b =>
      have hab : a ≠ b := fun h ↦ hnd₁ (by simp [h])
      by_cases ha : a ∈ f₂
      · by_cases hb : b ∈ f₂
        · exfalso; apply hne
          exact (Sym2.mem_and_mem_iff hab).mp ⟨ha, hb⟩ |>.symm
        · exact ⟨b, a, hab.symm, Sym2.eq_swap, hb⟩
      · exact ⟨a, b, hab, rfl, ha⟩
  have hleaf : ∀ e ∈ ({s(ℓ, u), f₂} : Finset (Sym2 V)), ℓ ∈ e → e = s(ℓ, u) := by
    intro e he hℓe
    rcases Finset.mem_insert.mp he with h | h
    · exact h
    · rw [Finset.mem_singleton.mp h] at hℓe; exact absurd hℓe hℓ
  unfold forestDens
  rw [wInt_leaf _ _ _ hℓu (by simp) hleaf]
  have herase : ({s(ℓ, u), f₂} : Finset (Sym2 V)).erase s(ℓ, u) = {f₂} := by
    rw [Finset.erase_insert (by simpa using hne)]
  rw [herase]
  induction f₂ using Sym2.inductionOn with
  | _ c w =>
  have hcw : c ≠ w := fun h ↦ hnd₂ (by simp [h])
  have hℓc : ℓ ≠ c := fun h ↦ hℓ (by simp [h])
  have hℓw : ℓ ≠ w := fun h ↦ hℓ (by simp [h])
  by_cases hu : u ∈ s(c, w)
  · -- adjacent: the other end of `f₂` is a leaf hanging from `u`
    left
    refine ⟨⟨u, fun f hf ↦ ?_⟩, ?_⟩
    · rcases Finset.mem_insert.mp hf with h | h
      · rw [h]; simp
      · rw [Finset.mem_singleton.mp h]; exact hu
    obtain ⟨x, hx⟩ : ∃ x, s(c, w) = s(x, u) ∧ x ≠ u := by
      rcases Sym2.mem_iff.mp hu with rfl | rfl
      · exact ⟨w, Sym2.eq_swap, hcw.symm⟩
      · exact ⟨c, rfl, hcw⟩
    rw [hx.1]
    have hxℓ : x ≠ ℓ := by
      intro h; apply hℓ; rw [hx.1, h]; simp
    rw [wInt_leaf _ _ _ hx.2 (by simp) (fun e he _ ↦ Finset.mem_singleton.mp he),
      Finset.erase_singleton, wInt_empty]
    rw [← Finset.mul_prod_erase univ _ (mem_univ u)]
    have hrest : ∏ v ∈ univ.erase u, ∫ y, (Function.update (Function.update (Function.update
        (Function.update (fun _ ↦ BddFun.one) ℓ BddFun.one) u
          ((BddFun.one).mul (BddFun.apply U BddFun.one))) x BddFun.one) u
        ((Function.update (Function.update (fun _ ↦ BddFun.one) ℓ BddFun.one) u
          ((BddFun.one).mul (BddFun.apply U BddFun.one)) u).mul (BddFun.apply U
            ((Function.update (Function.update (fun _ ↦ BddFun.one) ℓ BddFun.one) u
              ((BddFun.one).mul (BddFun.apply U BddFun.one))) x)))) v y ∂μ = 1 := by
      refine Finset.prod_eq_one fun v hv ↦ ?_
      have hvu : v ≠ u := Finset.ne_of_mem_erase hv
      rw [Function.update_of_ne hvu]
      by_cases hvx : v = x
      · subst hvx; simp [BddFun.one]
      · rw [Function.update_of_ne hvx, Function.update_of_ne hvu]
        by_cases hvℓ : v = ℓ
        · subst hvℓ; simp [BddFun.one]
        · rw [Function.update_of_ne hvℓ]; simp [BddFun.one]
    rw [hrest, mul_one, Function.update_self]
    simp only [Function.update_self, Function.update_of_ne hx.2, Function.update_of_ne hxℓ,
      BddFun.mul_apply, BddFun.one_apply, BddFun.apply_apply, one_mul, mul_one]
    unfold Mom
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    simp only [degree]
    ring
  · -- disjoint: integrate a leaf of `f₂`
    right
    refine ⟨fun ⟨v, hv⟩ ↦ ?_, ?_⟩
    · have h1 := hv _ (Finset.mem_insert_self _ _)
      have h2 := hv _ (by simp : s(c, w) ∈ ({s(ℓ, u), s(c, w)} : Finset (Sym2 V)))
      rcases Sym2.mem_iff.mp h1 with rfl | rfl
      · exact hℓ h2
      · exact hu h2
    have hcu : c ≠ u := fun h ↦ hu (by simp [h])
    have hwu : w ≠ u := fun h ↦ hu (by simp [h])
    rw [wInt_leaf _ _ _ hcw (by simp) (fun e he _ ↦ Finset.mem_singleton.mp he),
      Finset.erase_singleton, wInt_empty]
    rw [← Finset.mul_prod_erase univ _ (mem_univ u)]
    have hwu' : w ∈ univ.erase u := Finset.mem_erase.mpr ⟨hwu, mem_univ w⟩
    rw [← Finset.mul_prod_erase _ _ hwu']
    have hrest : ∏ v ∈ (univ.erase u).erase w, ∫ y, (Function.update (Function.update
        (Function.update (Function.update (fun _ ↦ BddFun.one) ℓ BddFun.one) u
          ((BddFun.one).mul (BddFun.apply U BddFun.one))) c BddFun.one) w
        ((Function.update (Function.update (fun _ ↦ BddFun.one) ℓ BddFun.one) u
          ((BddFun.one).mul (BddFun.apply U BddFun.one)) w).mul (BddFun.apply U
            ((Function.update (Function.update (fun _ ↦ BddFun.one) ℓ BddFun.one) u
              ((BddFun.one).mul (BddFun.apply U BddFun.one))) c)))) v y ∂μ = 1 := by
      refine Finset.prod_eq_one fun v hv ↦ ?_
      have hvw : v ≠ w := Finset.ne_of_mem_erase hv
      have hvu : v ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hv)
      rw [Function.update_of_ne hvw]
      by_cases hvc : v = c
      · subst hvc; simp [BddFun.one]
      · rw [Function.update_of_ne hvc, Function.update_of_ne hvu]
        by_cases hvℓ : v = ℓ
        · subst hvℓ; simp [BddFun.one]
        · rw [Function.update_of_ne hvℓ]; simp [BddFun.one]
    rw [hrest, mul_one]
    have hcℓ : c ≠ ℓ := fun h ↦ hℓc h.symm
    simp only [Function.update_self, Function.update_of_ne hwu.symm, Function.update_of_ne hwu,
      Function.update_of_ne hcu, Function.update_of_ne hcℓ, Function.update_of_ne (Ne.symm hℓw),
      BddFun.mul_apply, BddFun.one_apply, BddFun.apply_apply, one_mul, mul_one]
    simp only [Function.update_of_ne hcu.symm, Function.update_self, BddFun.mul_apply,
      BddFun.one_apply, BddFun.apply_apply, one_mul, mul_one]
    unfold meanDeg degree
    ring

end Taeyoung.Paper.Eventual
