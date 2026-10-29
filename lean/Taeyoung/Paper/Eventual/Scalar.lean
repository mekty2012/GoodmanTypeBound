import Taeyoung.Paper.Eventual.L2
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The scalar moment comparison (`paper.pdf`, Lemma 4.8)

Let `2 ≤ a ≤ b`, `Δ > 0`, let `w ≥ 0` be a bounded weight with `∫ w = 1` (so `w dμ` is a
probability measure), let `0 ≤ d ≤ Δ`, and let `0 ≤ α ≤ ∫ d w`. Then

`∫ d^b w - α^b ≤ (b(b-1))/(a(a-1)) Δ^{b-a} (∫ d^a w - α^a)`.

We write `a = p + 2`, `b = p + r + 2` with natural-number indices `p, r` (this `p` is not
the edge density). The proof is the paper's: the function
`ψ(z) = c z^a - z^b`, `c = (b(b-1))/(a(a-1)) Δ^{b-a}` (the paper's `-f`), is convex and
nondecreasing on `[0, Δ]`; its tangent line at `m = ∫ d w` integrates to `∫ ψ(d) w ≥ ψ(m)`, and the tangent
line at `α` gives `ψ(m) ≥ ψ(α)`. (Jensen's inequality in tangent-line form.)

* `scalar_moment`: the comparison above;
* `jensen_pow`: `∫ d^a w ≥ α^a` (the nonnegativity of the bracket).
-/

open MeasureTheory Set

namespace Taeyoung.Paper.Eventual

/-- A convex function lies above its tangent lines. -/
lemma tangent_le_of_convexOn {S : Set ℝ} {f : ℝ → ℝ} {f' m z : ℝ} (hf : ConvexOn ℝ S f)
    (hm : m ∈ S) (hz : z ∈ S) (hd : HasDerivAt f f' m) : f m + f' * (z - m) ≤ f z := by
  rcases lt_trichotomy m z with h | rfl | h
  · have h1 := hf.le_slope_of_hasDerivAt hm hz h hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at h1
    linarith
  · simp
  · have h1 := hf.slope_le_of_hasDerivAt hz hm h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at h1
    linarith

lemma hasDerivAt_pow_succ (n : ℕ) (z : ℝ) :
    HasDerivAt (fun x : ℝ ↦ x ^ (n + 1)) (((n : ℝ) + 1) * z ^ n) z := by
  simpa using hasDerivAt_pow (n + 1) z

/-- The comparison constant `(b(b-1))/(a(a-1))` for `a = p + 2`, `b = p + r + 2`. -/
noncomputable def cmpConst (p r : ℕ) : ℝ :=
  (((p + r : ℕ) : ℝ) + 2) * (((p + r : ℕ) : ℝ) + 1) / (((p : ℝ) + 2) * ((p : ℝ) + 1))

lemma one_le_cmpConst (p r : ℕ) : 1 ≤ cmpConst p r := by
  unfold cmpConst
  have hp : (0 : ℝ) < ((p : ℝ) + 2) * ((p : ℝ) + 1) := by positivity
  rw [le_div_iff₀ hp, one_mul]
  have : (p : ℝ) ≤ ((p + r : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right p r
  nlinarith

section Psi

variable (p r : ℕ) (Δ : ℝ)

/-- `ψ(z) = c z^{p+2} - z^{p+r+2}`. -/
noncomputable def psiF (z : ℝ) : ℝ := cmpConst p r * Δ ^ r * z ^ (p + 2) - z ^ (p + r + 2)

/-- `ψ'(z)`. -/
noncomputable def psiD (z : ℝ) : ℝ :=
  cmpConst p r * Δ ^ r * (((p + 1 : ℕ) : ℝ) + 1) * z ^ (p + 1) -
    (((p + r + 1 : ℕ) : ℝ) + 1) * z ^ (p + r + 1)

/-- `ψ''(z)`. -/
noncomputable def psiDD (z : ℝ) : ℝ :=
  cmpConst p r * Δ ^ r * (((p + 1 : ℕ) : ℝ) + 1) * (((p : ℕ) : ℝ) + 1) * z ^ p -
    (((p + r + 1 : ℕ) : ℝ) + 1) * (((p + r : ℕ) : ℝ) + 1) * z ^ (p + r)

lemma hasDerivAt_psiF (z : ℝ) : HasDerivAt (psiF p r Δ) (psiD p r Δ z) z := by
  have h := ((hasDerivAt_pow_succ (p + 1) z).const_mul (cmpConst p r * Δ ^ r)).sub
    (hasDerivAt_pow_succ (p + r + 1) z)
  exact h.congr_deriv (by unfold psiD; ring)

lemma hasDerivAt_psiD (z : ℝ) : HasDerivAt (psiD p r Δ) (psiDD p r Δ z) z := by
  have h := ((hasDerivAt_pow_succ p z).const_mul
    (cmpConst p r * Δ ^ r * (((p + 1 : ℕ) : ℝ) + 1))).sub
    ((hasDerivAt_pow_succ (p + r) z).const_mul (((p + r + 1 : ℕ) : ℝ) + 1))
  exact h.congr_deriv (by unfold psiDD; ring)

variable {Δ}

/-- The key identity `c (p+2)(p+1) = (p+r+2)(p+r+1) Δ^r`. -/
lemma cmpConst_mul (p r : ℕ) :
    cmpConst p r * (((p + 1 : ℕ) : ℝ) + 1) * (((p : ℕ) : ℝ) + 1) =
      (((p + r + 1 : ℕ) : ℝ) + 1) * (((p + r : ℕ) : ℝ) + 1) := by
  unfold cmpConst
  have hp : ((p : ℝ) + 2) * ((p : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma psiDD_nonneg {z : ℝ} (hz : z ∈ Icc 0 Δ) : 0 ≤ psiDD p r Δ z := by
  obtain ⟨hz0, hzΔ⟩ := hz
  have hk := cmpConst_mul p r
  have hzr : z ^ r ≤ Δ ^ r := pow_le_pow_left₀ hz0 hzΔ r
  have hzp : 0 ≤ z ^ p := pow_nonneg hz0 p
  have hpos : 0 ≤ (((p + r + 1 : ℕ) : ℝ) + 1) * (((p + r : ℕ) : ℝ) + 1) := by positivity
  have : psiDD p r Δ z =
      (((p + r + 1 : ℕ) : ℝ) + 1) * (((p + r : ℕ) : ℝ) + 1) * z ^ p * (Δ ^ r - z ^ r) := by
    unfold psiDD
    rw [show cmpConst p r * Δ ^ r * (((p + 1 : ℕ) : ℝ) + 1) * (((p : ℕ) : ℝ) + 1) * z ^ p =
      (cmpConst p r * (((p + 1 : ℕ) : ℝ) + 1) * (((p : ℕ) : ℝ) + 1)) * Δ ^ r * z ^ p by ring,
      hk, pow_add]
    ring
  rw [this]
  exact mul_nonneg (mul_nonneg hpos hzp) (sub_nonneg.mpr hzr)

lemma psiD_nonneg (hΔ : 0 ≤ Δ) {z : ℝ} (hz : z ∈ Icc 0 Δ) : 0 ≤ psiD p r Δ z := by
  obtain ⟨hz0, hzΔ⟩ := hz
  have hk := cmpConst_mul p r
  have hzr : z ^ r ≤ Δ ^ r := pow_le_pow_left₀ hz0 hzΔ r
  have hzp : 0 ≤ z ^ (p + 1) := pow_nonneg hz0 _
  have hΔr : 0 ≤ Δ ^ r := pow_nonneg hΔ r
  -- `c (p+2) = (p+r+2)(p+r+1)/(p+1) Δ^r ≥ (p+r+2) Δ^r`
  have hp1 : (0 : ℝ) < ((p : ℕ) : ℝ) + 1 := by positivity
  have hc : (((p + r + 1 : ℕ) : ℝ) + 1) ≤ cmpConst p r * (((p + 1 : ℕ) : ℝ) + 1) := by
    have hle : (((p : ℕ) : ℝ) + 1) ≤ (((p + r : ℕ) : ℝ) + 1) := by
      have : ((p : ℕ) : ℝ) ≤ ((p + r : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right p r
      linarith
    have h2 : (((p + r + 1 : ℕ) : ℝ) + 1) * (((p : ℕ) : ℝ) + 1) ≤
        cmpConst p r * (((p + 1 : ℕ) : ℝ) + 1) * (((p : ℕ) : ℝ) + 1) := by
      rw [hk]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    exact le_of_mul_le_mul_right h2 hp1
  have : psiD p r Δ z = z ^ (p + 1) *
      (cmpConst p r * (((p + 1 : ℕ) : ℝ) + 1) * Δ ^ r - (((p + r + 1 : ℕ) : ℝ) + 1) * z ^ r) := by
    unfold psiD
    rw [show p + r + 1 = (p + 1) + r by ring, pow_add]
    ring
  rw [this]
  refine mul_nonneg hzp (sub_nonneg.mpr ?_)
  calc (((p + r + 1 : ℕ) : ℝ) + 1) * z ^ r ≤ (((p + r + 1 : ℕ) : ℝ) + 1) * Δ ^ r :=
        mul_le_mul_of_nonneg_left hzr (by positivity)
    _ ≤ cmpConst p r * (((p + 1 : ℕ) : ℝ) + 1) * Δ ^ r := mul_le_mul_of_nonneg_right hc hΔr

lemma convexOn_psiF (hΔ : 0 ≤ Δ) : ConvexOn ℝ (Icc 0 Δ) (psiF p r Δ) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 Δ) (f' := psiD p r Δ)
    (f'' := psiDD p r Δ) ?_ ?_ ?_ ?_
  · exact fun z _ ↦ (hasDerivAt_psiF p r Δ z).continuousAt.continuousWithinAt
  · exact fun z _ ↦ (hasDerivAt_psiF p r Δ z).hasDerivWithinAt
  · exact fun z _ ↦ (hasDerivAt_psiD p r Δ z).hasDerivWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    exact psiDD_nonneg p r (Ioo_subset_Icc_self hz)

end Psi

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma isBdd_npow {f : Ω → ℝ} (hf : IsBdd f) : ∀ k : ℕ, IsBdd (fun x ↦ f x ^ k)
  | 0 => by simpa using IsBdd.const (Ω := Ω) 1
  | k + 1 => by simpa [pow_succ] using (isBdd_npow hf k).mul hf

/-- **Lemma 4.8.** For a weight `w ≥ 0` with `∫ w = 1`, `0 ≤ d ≤ Δ` and
`0 ≤ α ≤ ∫ d w`: `∫ d^b w - α^b ≤ C Δ^{b-a} (∫ d^a w - α^a)`, with `a = p + 2`,
`b = p + r + 2` and `C = cmpConst p r = (b(b-1))/(a(a-1))`. -/
theorem scalar_moment {d w : Ω → ℝ} (hd : IsBdd d) (hw : IsBdd w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∫ x, w x ∂μ = 1) {Δ : ℝ} (hΔ : 0 ≤ Δ) (hd0 : ∀ x, 0 ≤ d x) (hdΔ : ∀ x, d x ≤ Δ)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ ∫ x, d x * w x ∂μ) (p r : ℕ) :
    (∫ x, d x ^ (p + r + 2) * w x ∂μ) - α ^ (p + r + 2) ≤
      cmpConst p r * Δ ^ r * ((∫ x, d x ^ (p + 2) * w x ∂μ) - α ^ (p + 2)) := by
  set m := ∫ x, d x * w x ∂μ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun x ↦ mul_nonneg (hd0 x) (hw0 x)
  have hmΔ : m ≤ Δ := by
    calc m ≤ ∫ x, Δ * w x ∂μ :=
          integral_mono (hd.mul hw).integrable (hw.smul Δ).integrable
            fun x ↦ mul_le_mul_of_nonneg_right (hdΔ x) (hw0 x)
      _ = Δ := by rw [integral_const_mul, hw1, mul_one]
  have hmI : m ∈ Icc 0 Δ := ⟨hm0, hmΔ⟩
  have hαI : α ∈ Icc 0 Δ := ⟨hα0, hα.trans hmΔ⟩
  have hconv := convexOn_psiF p r hΔ
  set c := cmpConst p r * Δ ^ r with hc
  -- tangent at `m`, integrated
  have hpt : ∀ x, (psiF p r Δ m + psiD p r Δ m * (d x - m)) * w x ≤
      psiF p r Δ (d x) * w x := fun x ↦
    mul_le_mul_of_nonneg_right
      (tangent_le_of_convexOn hconv hmI ⟨hd0 x, hdΔ x⟩ (hasDerivAt_psiF p r Δ m)) (hw0 x)
  have hda : IsBdd (fun x ↦ d x ^ (p + 2) * w x) := (isBdd_npow hd (p + 2)).mul hw
  have hdb : IsBdd (fun x ↦ d x ^ (p + r + 2) * w x) := (isBdd_npow hd (p + r + 2)).mul hw
  have hdw : IsBdd (fun x ↦ d x * w x) := hd.mul hw
  have hL : ∫ x, (psiF p r Δ m + psiD p r Δ m * (d x - m)) * w x ∂μ = psiF p r Δ m := by
    have : (fun x ↦ (psiF p r Δ m + psiD p r Δ m * (d x - m)) * w x) =
        fun x ↦ (psiF p r Δ m - psiD p r Δ m * m) * w x + psiD p r Δ m * (d x * w x) := by
      funext x; ring
    rw [this, integral_add ((hw.smul _).integrable) ((hdw.smul _).integrable),
      integral_const_mul, integral_const_mul, hw1, ← hm]
    ring
  have hR : ∫ x, psiF p r Δ (d x) * w x ∂μ =
      c * (∫ x, d x ^ (p + 2) * w x ∂μ) - ∫ x, d x ^ (p + r + 2) * w x ∂μ := by
    have : (fun x ↦ psiF p r Δ (d x) * w x) =
        fun x ↦ c * (d x ^ (p + 2) * w x) - d x ^ (p + r + 2) * w x := by
      funext x; unfold psiF; rw [← hc]; ring
    rw [this, integral_sub ((hda.smul c).integrable) hdb.integrable, integral_const_mul]
  have hint : psiF p r Δ m ≤ ∫ x, psiF p r Δ (d x) * w x ∂μ := by
    rw [← hL]
    refine integral_mono ?_ ?_ hpt
    · exact ((hw.smul (psiF p r Δ m)).add
        (((hd.sub (IsBdd.const m)).mul hw).smul (psiD p r Δ m))).integrable.congr
        (ae_of_all _ fun x ↦ by simp only []; ring)
    · exact ((hda.smul c).sub hdb).integrable.congr
        (ae_of_all _ fun x ↦ by simp only [psiF]; rw [← hc]; ring)
  -- tangent at `α`, evaluated at `m`
  have hmono : psiF p r Δ α ≤ psiF p r Δ m := by
    have h1 := tangent_le_of_convexOn hconv hαI hmI (hasDerivAt_psiF p r Δ α)
    have h2 : 0 ≤ psiD p r Δ α * (m - α) := mul_nonneg (psiD_nonneg p r hΔ hαI) (by linarith)
    linarith
  have hfin := hmono.trans (hint.trans (le_of_eq hR))
  unfold psiF at hfin
  rw [← hc] at hfin
  linarith

/-- `∫ d^a w ≥ α^a` for `0 ≤ α ≤ ∫ d w` (Jensen for `z ↦ z^a`). -/
theorem jensen_pow {d w : Ω → ℝ} (hd : IsBdd d) (hw : IsBdd w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∫ x, w x ∂μ = 1) (hd0 : ∀ x, 0 ≤ d x)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ ∫ x, d x * w x ∂μ) (n : ℕ) :
    α ^ (n + 1) ≤ ∫ x, d x ^ (n + 1) * w x ∂μ := by
  set m := ∫ x, d x * w x ∂μ with hm
  have hm0 : 0 ≤ m := hα0.trans hα
  have hconv : ConvexOn ℝ (Ici 0) (fun z : ℝ ↦ z ^ (n + 1)) := convexOn_pow (n + 1)
  have hpt : ∀ x, (m ^ (n + 1) + ((n : ℝ) + 1) * m ^ n * (d x - m)) * w x ≤
      d x ^ (n + 1) * w x := fun x ↦
    mul_le_mul_of_nonneg_right
      (tangent_le_of_convexOn hconv (mem_Ici.mpr hm0) (mem_Ici.mpr (hd0 x))
        (hasDerivAt_pow_succ n m)) (hw0 x)
  have hdw : IsBdd (fun x ↦ d x * w x) := hd.mul hw
  have hL : ∫ x, (m ^ (n + 1) + ((n : ℝ) + 1) * m ^ n * (d x - m)) * w x ∂μ = m ^ (n + 1) := by
    have : (fun x ↦ (m ^ (n + 1) + ((n : ℝ) + 1) * m ^ n * (d x - m)) * w x) =
        fun x ↦ (m ^ (n + 1) - ((n : ℝ) + 1) * m ^ n * m) * w x +
          ((n : ℝ) + 1) * m ^ n * (d x * w x) := by
      funext x; ring
    rw [this, integral_add ((hw.smul _).integrable) ((hdw.smul _).integrable),
      integral_const_mul, integral_const_mul, hw1, ← hm]
    ring
  have hint : m ^ (n + 1) ≤ ∫ x, d x ^ (n + 1) * w x ∂μ := by
    rw [← hL]
    refine integral_mono ?_ ((isBdd_npow hd (n + 1)).mul hw).integrable hpt
    exact ((hw.smul (m ^ (n + 1))).add
      (((hd.sub (IsBdd.const m)).mul hw).smul (((n : ℝ) + 1) * m ^ n))).integrable.congr
      (ae_of_all _ fun x ↦ by simp only []; ring)
  exact (pow_le_pow_left₀ hα0 hα (n + 1)).trans hint

end Taeyoung.Paper.Eventual
