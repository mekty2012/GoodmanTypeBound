import Taeyoung.Paper.Eventual.Kernels
import Taeyoung.Paper.Eventual.Scalar
import OddCycleBound.IntermediateRegion.TracePowers
import OddCycleBound.IntermediateRegion.CenteredOperator

/-!
# A cycle comparison for arbitrary graphons (`paper.pdf`, Theorem 4.7)

For a graphon `U` with `d ≤ Δ`, odd `g ≥ 5` and an integer `s ≥ g`,

`0 ≤ S_g(U)` and `S_s(U) ≤ (b(b-1))/(a(a-1)) Δ^{s-g} S_g(U)`, `a = g - 2`, `b = s - 2`,

where `S_s = M_{s-1} - t(C_s,U)` (`Ss`).  In Lean `g = p + 4` and `s = g + r` for
natural-number indices `p` (odd) and `r`; this `p` is not the edge density.  The paper
also states `0 ≤ S_s`; `cycle_comparison` records nonnegativity only for `S_g`.

The graphon operator `T` on `L²(μ)` is compact and self-adjoint (`kernelOpCLM_isCompact`,
`kernelOpCLM_isSymmetric` from `OddCycleBound`); `(λ_i, f_i)` are its nonzero eigenvalues
with an orthonormal family of eigenvectors (`OddCycleBound`'s `nonzeroEigenmode`). We use the bounded
representatives `φ_i(x) = ∫ U(x,y) f_i(y) dy = ⟨row_x, f_i⟩` of `λ_i f_i`.

* `abs_eigen_le`: `|λ| ≤ ∫ d g²` for a normalised eigenfunction ((4.19),
  (4.16));
* `hasSum_cyc`: the trace formula `t(C_{k+3},U) = Σ λ_i^{k+3}` (4.17);
* `tsum_weighted_le`: the weighted Bessel inequality `Σ_i ∫ w φ_i² ≤ ∫ w(x) ‖row_x‖²` for
  `w ≥ 0`. The paper uses the equality (4.18), proved by completing the
  `f_i` with an orthonormal basis of `ker T_U`; we avoid that completion and keep the
  (nonnegative) Bessel residual `Res` as an extra term instead;
* `Ss_decomp`: **Lemma 4.10** (with the residual):
  `S_{k+3} = ∫ d^{k+1} U(1-U) + Res_{k+1} + Σ_i (∫ d^{k+1} φ_i² - λ_i^{k+3})`;
* `cycle_comparison`: **Theorem 4.7**.
-/

open MeasureTheory Finset

namespace Taeyoung.Paper.Eventual

open Taeyoung
open OddCycleBound.Spectral.L2Kernel OddCycleBound.IntermediateRegion
  OddCycleBound.Spectral.InfiniteSpectral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Laplacian

variable (U : Graphon Ω μ)

/-- **(4.19).** If `∫ U(x,y) g(y) dy = c g(x)` for every `x` and
`∫ g² = 1`, then `|c| ≤ ∫ d g²`. -/
theorem abs_eigen_le {g : Ω → ℝ} (hg : IsBdd g) {c : ℝ}
    (heig : ∀ x, ∫ y, U x y * g y ∂μ = c * g x) (hg1 : ∫ x, g x ^ 2 ∂μ = 1) :
    |c| ≤ ∫ x, degree U x * g x ^ 2 ∂μ := by
  have hU := Bdd2.graphon U
  have hA : Bdd2 (fun x y ↦ U x y * g x ^ 2) := hU.mul (Bdd2.left hg.sq)
  have hB : Bdd2 (fun x y ↦ U x y * (g x * g y)) := hU.mul ((Bdd2.left hg).mul (Bdd2.right hg))
  have hC : Bdd2 (fun x y ↦ U x y * g y ^ 2) := hU.mul (Bdd2.right hg.sq)
  have hP : dint μ (fun x y ↦ U x y * (g x * g y)) = c := by
    unfold dint
    calc ∫ x, ∫ y, U x y * (g x * g y) ∂μ ∂μ = ∫ x, c * g x ^ 2 ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
          simp only []
          calc ∫ y, U x y * (g x * g y) ∂μ = ∫ y, g x * (U x y * g y) ∂μ :=
                integral_congr_ae (ae_of_all _ fun y ↦ by ring)
            _ = c * g x ^ 2 := by rw [integral_const_mul, heig x]; ring
      _ = c := by rw [integral_const_mul, hg1, mul_one]
  have hQ : dint μ (fun x y ↦ U x y * g x ^ 2) = ∫ x, degree U x * g x ^ 2 ∂μ := by
    unfold dint
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only []
    rw [integral_mul_const]; rfl
  have hQ' : dint μ (fun x y ↦ U x y * g y ^ 2) = ∫ x, degree U x * g x ^ 2 ∂μ := by
    rw [dint_swap hC]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    simp only []
    rw [integral_mul_const]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun x ↦ U.symm x y)
  have hsq : ∀ s : ℝ, dint μ (fun x y ↦ U x y * (g x + s * g y) ^ 2) =
      dint μ (fun x y ↦ U x y * g x ^ 2) + 2 * s * dint μ (fun x y ↦ U x y * (g x * g y)) +
        s ^ 2 * dint μ (fun x y ↦ U x y * g y ^ 2) := by
    intro s
    have h1 : (fun x y ↦ U x y * (g x + s * g y) ^ 2) = fun x y ↦
        (U x y * g x ^ 2 + (2 * s) * (U x y * (g x * g y))) + s ^ 2 * (U x y * g y ^ 2) := by
      funext x y; ring
    rw [h1, dint_add (hA.add (hB.smul _)) (hC.smul _), dint_add hA (hB.smul _), dint_smul,
      dint_smul]
  have hp := hsq 1
  have hm := hsq (-1)
  have hp0 : 0 ≤ dint μ (fun x y ↦ U x y * (g x + 1 * g y) ^ 2) :=
    dint_nonneg fun x y ↦ mul_nonneg (U.nonneg x y) (sq_nonneg _)
  have hm0 : 0 ≤ dint μ (fun x y ↦ U x y * (g x + -1 * g y) ^ 2) :=
    dint_nonneg fun x y ↦ mul_nonneg (U.nonneg x y) (sq_nonneg _)
  rw [hP, hQ, hQ'] at hp hm
  rw [abs_le]
  constructor <;> nlinarith

end Laplacian

section Spectral

variable (U : Graphon Ω μ)

/-- The graphon operator `T_U` on `L²(μ)`. -/
noncomputable abbrev gOp : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  kernelOpCLM (mu := μ) (Paper.isGraphon_ofFoundation U)

lemma gOp_compact : IsCompactOperator (gOp U) := kernelOpCLM_isCompact _

lemma gOp_symm : (gOp U : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := kernelOpCLM_isSymmetric _

/-- Indices of the nonzero eigenvalues of `T_U`, with multiplicity. -/
abbrev EIdx := NonzeroEigenIndex (gOp U)

lemma countable_EIdx : Countable (EIdx U) :=
  nonzeroEigenIndex_countable _ (gOp_compact U) (gOp_symm U)

/-- The nonzero eigenvalues `λ_i`. -/
noncomputable def ev (i : EIdx U) : ℝ := nonzeroEigenvalue (gOp U) i

/-- An orthonormal family of eigenvectors `f_i`. -/
noncomputable def emode (i : EIdx U) : Lp ℝ 2 μ := nonzeroEigenmode (gOp U) (gOp_compact U) i

lemma emode_orthonormal : Orthonormal ℝ (emode U) :=
  nonzeroEigenmode_orthonormal (gOp U) (gOp_compact U) (gOp_symm U)

lemma emode_diag (i : EIdx U) : gOp U (emode U i) = ev U i • emode U i :=
  nonzeroEigenmode_diagonal _ _ i

lemma ev_ne (i : EIdx U) : ev U i ≠ 0 := nonzeroEigenvalue_ne _ i

/-- The row `y ↦ U(x,y)` in `L²`. -/
noncomputable abbrev rowL2 (x : Ω) : Lp ℝ 2 μ := goodL2 (mu := μ) (goodK_row (goodK_U U) x)

lemma inner_rowL2 (x : Ω) (f : Lp ℝ 2 μ) :
    inner ℝ (rowL2 U x) f = ∫ y, U x y * f y ∂μ :=
  inner_goodK_row_l2_eq_kernelOp (mu := μ) (goodK_U U) f x

lemma gOp_ae (f : Lp ℝ 2 μ) : (gOp U f : Ω → ℝ) =ᵐ[μ] fun x ↦ ∫ y, U x y * f y ∂μ := by
  have hW := Paper.isGraphon_ofFoundation U
  have h1 := kernelOpCLM_eq_kernelOpGoodKCLM (mu := μ) hW
  have h2 := kernelOpGoodKCLM_eq_kernelOpGoodKL2OfL2_apply (mu := μ) (goodK_U U) zero_le_one
    (graphon_abs_le_one (mu := μ) hW) U.symm f
  show ((kernelOpCLM (mu := μ) hW f : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] _
  rw [h1]
  erw [h2]
  exact goodL2_ae_eq (mu := μ) _

/-- `φ_i(x) = ∫ U(x,y) f_i(y) dy`, the bounded representative of `λ_i f_i`. -/
noncomputable def phi (i : EIdx U) (x : Ω) : ℝ := ∫ y, U x y * emode U i y ∂μ

lemma phi_eq_inner (i : EIdx U) (x : Ω) : phi U i x = inner ℝ (rowL2 U x) (emode U i) :=
  (inner_rowL2 U x _).symm

lemma isBdd_phi (i : EIdx U) : IsBdd (phi U i) := by
  have h := good_kernelOp_goodK_l2 (mu := μ) (goodK_U U) zero_le_one
    (graphon_abs_le_one (mu := μ) (Paper.isGraphon_ofFoundation U)) (emode U i)
  obtain ⟨C, -, hC⟩ := h.bdd
  exact ⟨h.meas.measurable, C, hC⟩

lemma phi_ae (i : EIdx U) : phi U i =ᵐ[μ] fun x ↦ ev U i * emode U i x := by
  have h1 := gOp_ae U (emode U i)
  rw [emode_diag] at h1
  filter_upwards [h1, Lp.coeFn_smul (ev U i) (emode U i)] with x hx hs
  show ∫ y, U x y * emode U i y ∂μ = _
  rw [← hx, hs]
  rfl

lemma integral_emode_sq (i : EIdx U) : ∫ x, (emode U i x) ^ 2 ∂μ = 1 := by
  have h := (emode_orthonormal U).norm_eq_one i
  have h2 : inner ℝ (emode U i) (emode U i) = ∫ x, (emode U i x) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [← h2, real_inner_self_eq_norm_sq, h, one_pow]

lemma integral_phi_sq (i : EIdx U) : ∫ x, phi U i x ^ 2 ∂μ = ev U i ^ 2 := by
  calc ∫ x, phi U i x ^ 2 ∂μ = ∫ x, ev U i ^ 2 * emode U i x ^ 2 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [phi_ae U i] with x hx
        rw [hx]; ring
    _ = ev U i ^ 2 := by rw [integral_const_mul, integral_emode_sq, mul_one]

/-- The eigenvalue equation holds everywhere for `φ_i`. -/
lemma phi_eigen (i : EIdx U) (x : Ω) : ∫ y, U x y * phi U i y ∂μ = ev U i * phi U i x := by
  calc ∫ y, U x y * phi U i y ∂μ = ∫ y, ev U i * (U x y * emode U i y) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [phi_ae U i] with y hy
        rw [hy]; ring
    _ = ev U i * phi U i x := by rw [integral_const_mul]; rfl

/-- The normalised eigenfunction `g_i = λ_i⁻¹ φ_i`. -/
noncomputable def gN (i : EIdx U) (x : Ω) : ℝ := (ev U i)⁻¹ * phi U i x

lemma isBdd_gN (i : EIdx U) : IsBdd (gN U i) := (isBdd_phi U i).smul _

lemma phi_eq_gN (i : EIdx U) (x : Ω) : phi U i x = ev U i * gN U i x := by
  unfold gN; field_simp [ev_ne U i]

lemma gN_eigen (i : EIdx U) (x : Ω) : ∫ y, U x y * gN U i y ∂μ = ev U i * gN U i x := by
  unfold gN
  calc ∫ y, U x y * ((ev U i)⁻¹ * phi U i y) ∂μ = (ev U i)⁻¹ * ∫ y, U x y * phi U i y ∂μ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun y ↦ by ring)
    _ = _ := by rw [phi_eigen]; ring

lemma integral_gN_sq (i : EIdx U) : ∫ x, gN U i x ^ 2 ∂μ = 1 := by
  unfold gN
  have : (fun x ↦ ((ev U i)⁻¹ * phi U i x) ^ 2) = fun x ↦ ((ev U i)⁻¹) ^ 2 * phi U i x ^ 2 := by
    funext x; ring
  rw [this, integral_const_mul, integral_phi_sq, ← mul_pow, inv_mul_cancel₀ (ev_ne U i),
    one_pow]

/-- **(4.16)**: `|λ_i| ≤ ∫ d g_i²`. -/
lemma abs_ev_le (i : EIdx U) : |ev U i| ≤ ∫ x, degree U x * gN U i x ^ 2 ∂μ :=
  abs_eigen_le U (isBdd_gN U i) (gN_eigen U i) (integral_gN_sq U i)

lemma integral_deg_gN_le {Δ : ℝ} (hdeg : ∀ x, degree U x ≤ Δ) (i : EIdx U) :
    ∫ x, degree U x * gN U i x ^ 2 ∂μ ≤ Δ := by
  calc ∫ x, degree U x * gN U i x ^ 2 ∂μ ≤ ∫ x, Δ * gN U i x ^ 2 ∂μ :=
        integral_mono ((isBdd_degree U).mul (isBdd_gN U i).sq).integrable
          ((isBdd_gN U i).sq.smul Δ).integrable
          fun x ↦ mul_le_mul_of_nonneg_right (hdeg x) (sq_nonneg _)
    _ = Δ := by rw [integral_const_mul, integral_gN_sq, mul_one]

lemma abs_ev_le_one (i : EIdx U) : |ev U i| ≤ 1 :=
  (abs_ev_le U i).trans (integral_deg_gN_le U (degree_le_one U) i)

/-! ### Bessel's inequality for the rows -/

/-- `‖row_x‖² = ∫ U(x,y)² dy`. -/
noncomputable def rowSq (x : Ω) : ℝ := ∫ y, U x y * U x y ∂μ

lemma isBdd_rowSq : IsBdd (rowSq U) := ((Bdd2.graphon U).mul (Bdd2.graphon U)).inner

lemma inner_rowL2_self (x : Ω) : inner ℝ (rowL2 U x) (rowL2 U x) = rowSq U x := by
  rw [inner_rowL2]
  refine integral_congr_ae ?_
  filter_upwards [goodL2_ae_eq (mu := μ) (goodK_row (goodK_U U) x)] with y hy
  rw [hy]

lemma sum_phi_sq_le (x : Ω) (s : Finset (EIdx U)) : ∑ i ∈ s, phi U i x ^ 2 ≤ rowSq U x := by
  have h := sum_inner_sq_le_self_of_orthonormal (emode_orthonormal U) (rowL2 U x) s
  rw [inner_rowL2_self] at h
  simpa only [← phi_eq_inner] using h

lemma sum_weighted_le {w : Ω → ℝ} (hw : IsBdd w) (hw0 : ∀ x, 0 ≤ w x) (s : Finset (EIdx U)) :
    ∑ i ∈ s, ∫ x, w x * phi U i x ^ 2 ∂μ ≤ ∫ x, w x * rowSq U x ∂μ := by
  have hint : ∀ i ∈ s, Integrable (fun x ↦ w x * phi U i x ^ 2) μ :=
    fun i _ ↦ (hw.mul (isBdd_phi U i).sq).integrable
  rw [← integral_finsetSum s hint]
  refine integral_mono (integrable_finsetSum s hint) (hw.mul (isBdd_rowSq U)).integrable
    fun x ↦ ?_
  simp only []
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_phi_sq_le U x s) (hw0 x)

lemma summable_weighted {w : Ω → ℝ} (hw : IsBdd w) (hw0 : ∀ x, 0 ≤ w x) :
    Summable fun i : EIdx U ↦ ∫ x, w x * phi U i x ^ 2 ∂μ :=
  summable_of_sum_le (fun _ ↦ integral_nonneg fun x ↦ mul_nonneg (hw0 x) (sq_nonneg _))
    (sum_weighted_le U hw hw0)

/-- The weighted Bessel inequality. -/
lemma tsum_weighted_le {w : Ω → ℝ} (hw : IsBdd w) (hw0 : ∀ x, 0 ≤ w x) :
    ∑' i : EIdx U, ∫ x, w x * phi U i x ^ 2 ∂μ ≤ ∫ x, w x * rowSq U x ∂μ :=
  Real.tsum_le_of_sum_le (fun _ ↦ integral_nonneg fun x ↦ mul_nonneg (hw0 x) (sq_nonneg _))
    (sum_weighted_le U hw hw0)

lemma summable_ev_sq : Summable fun i : EIdx U ↦ ev U i ^ 2 := by
  have h := summable_weighted U (IsBdd.const 1) (fun _ ↦ zero_le_one)
  refine h.congr fun i ↦ ?_
  simp only [one_mul]
  exact integral_phi_sq U i

/-! ### The trace formula -/

/-- **(4.17)**: `t(C_{k+3},U) = Σ_i λ_i^{k+3}`. -/
theorem hasSum_cyc (k : ℕ) : HasSum (fun i : EIdx U ↦ ev U i ^ (k + 3)) (cyc U (k + 3)) := by
  haveI := countable_EIdx U
  have hW := Paper.isGraphon_ofFoundation U
  have htr := trace_compPow_eq_integral_row_inner_goodK_clmIter (mu := μ) (goodK_U U)
    zero_le_one (graphon_abs_le_one (mu := μ) hW) U.symm k
  rw [← kernelOpCLM_eq_kernelOpGoodKCLM (mu := μ) hW] at htr
  have hcyc : cyc U (k + 3) = OddCycleBound.trace μ (OddCycleBound.compPow μ U.toFun (k + 2)) :=
    rfl
  have hquad : ∀ x, HasSum (fun i ↦ ev U i ^ (k + 1) * phi U i x ^ 2)
      (inner ℝ (rowL2 U x) (clmIter (mu := μ) (gOp U) (k + 1) (rowL2 U x))) := by
    intro x
    have h := indexed_quadratic_expansion_iter (gOp U) (emode U) (ev U) (emode_diag U)
      (fun f ↦ compactSelfAdjoint_action_expansion (gOp U) (gOp_compact U) (gOp_symm U) f) k
      (rowL2 U x)
    rw [opIter_eq_l2_clmIter] at h
    simpa only [← phi_eq_inner] using h
  set F : EIdx U → Ω → ℝ := fun i x ↦ ev U i ^ (k + 1) * phi U i x ^ 2 with hFdef
  have hF : ∀ i, Integrable (F i) μ := fun i ↦ ((isBdd_phi U i).sq.smul _).integrable
  have hnorm : ∀ i, ∫ x, ‖F i x‖ ∂μ ≤ ev U i ^ 2 := by
    intro i
    have h1 : ∀ x, ‖F i x‖ = |ev U i| ^ (k + 1) * phi U i x ^ 2 := by
      intro x
      simp only [hFdef, Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
    simp_rw [h1]
    rw [integral_const_mul, integral_phi_sq]
    have h2 : |ev U i| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_ev_le_one U i)
    nlinarith [sq_nonneg (ev U i)]
  have hsum : Summable fun i ↦ ∫ x, ‖F i x‖ ∂μ :=
    (summable_ev_sq U).of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hnorm
  have hser := hasSum_integral_of_summable_integral_norm hF hsum
  have htsum : (fun x ↦ ∑' i, F i x) =
      fun x ↦ inner ℝ (rowL2 U x) (clmIter (mu := μ) (gOp U) (k + 1) (rowL2 U x)) :=
    funext fun x ↦ (hquad x).tsum_eq
  rw [htsum, ← htr, ← hcyc] at hser
  refine hser.congr_fun fun i ↦ ?_
  show ev U i ^ (k + 3) = ∫ x, ev U i ^ (k + 1) * phi U i x ^ 2 ∂μ
  rw [integral_const_mul, integral_phi_sq]
  ring

/-! ### The nonnegative decomposition -/

/-- `∫ d(x)^j ∫ U(x,y)(1-U(x,y)) dy dx`. -/
noncomputable def Apart (j : ℕ) : ℝ :=
  ∫ x, degree U x ^ j * ∫ y, U x y * (1 - U x y) ∂μ ∂μ

/-- The Bessel residual `∫ d^j ‖row_x‖² - Σ_i ∫ d^j φ_i² ≥ 0`. -/
noncomputable def Res (j : ℕ) : ℝ :=
  (∫ x, degree U x ^ j * rowSq U x ∂μ) - ∑' i : EIdx U, ∫ x, degree U x ^ j * phi U i x ^ 2 ∂μ

/-- The eigenvalue terms `λ_i² (∫ d^{k+1} g_i² - λ_i^{k+1}) = ∫ d^{k+1} φ_i² - λ_i^{k+3}`. -/
noncomputable def term (i : EIdx U) (k : ℕ) : ℝ :=
  (∫ x, degree U x ^ (k + 1) * phi U i x ^ 2 ∂μ) - ev U i ^ (k + 3)

lemma isBdd_one_sub_row : IsBdd (fun x ↦ ∫ y, U x y * (1 - U x y) ∂μ) :=
  ((Bdd2.graphon U).mul (bdd2_one_sub U)).inner

lemma isBdd_degPow (j : ℕ) : IsBdd (fun x ↦ degree U x ^ j) := isBdd_npow (isBdd_degree U) j

lemma summable_term (k : ℕ) : Summable fun i : EIdx U ↦ term U i k :=
  (summable_weighted U (isBdd_degPow U (k + 1))
    (fun x ↦ pow_nonneg (degree_nonneg U x) _)).sub (hasSum_cyc U k).summable

/-- **Lemma 4.10** (with the Bessel residual). -/
theorem Ss_decomp (k : ℕ) :
    Ss U (k + 3) = Apart U (k + 1) + Res U (k + 1) + ∑' i : EIdx U, term U i k := by
  have hpt : ∀ x, degree U x = (∫ y, U x y * (1 - U x y) ∂μ) + rowSq U x := by
    intro x
    unfold rowSq degree
    rw [← integral_add (((isBdd_row U x).mul ((IsBdd.const 1).sub (isBdd_row U x))).integrable)
      (((isBdd_row U x).mul (isBdd_row U x)).integrable)]
    exact integral_congr_ae (ae_of_all _ fun y ↦ by simp only []; ring)
  have hMom : Mom U (k + 2) = Apart U (k + 1) + ∫ x, degree U x ^ (k + 1) * rowSq U x ∂μ := by
    unfold Mom Apart
    rw [← integral_add ((isBdd_degPow U (k + 1)).mul (isBdd_one_sub_row U)).integrable
      ((isBdd_degPow U (k + 1)).mul (isBdd_rowSq U)).integrable]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only []
    rw [pow_succ, ← mul_add, ← hpt x]
  have hcyc := (hasSum_cyc U k).tsum_eq
  have hT : ∑' i : EIdx U, term U i k =
      (∑' i : EIdx U, ∫ x, degree U x ^ (k + 1) * phi U i x ^ 2 ∂μ) -
        ∑' i : EIdx U, ev U i ^ (k + 3) :=
    Summable.tsum_sub (summable_weighted U (isBdd_degPow U (k + 1))
      (fun x ↦ pow_nonneg (degree_nonneg U x) _)) (hasSum_cyc U k).summable
  show Mom U (k + 2) - cyc U (k + 3) = _
  rw [hMom, hT, hcyc, Res]
  ring

/-! ### The comparison -/

section Compare

variable {U} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hdeg : ∀ x, degree U x ≤ Δ)
include hΔ hdeg

lemma degPow_le (x : Ω) (a r : ℕ) : degree U x ^ (a + r) ≤ Δ ^ r * degree U x ^ a := by
  rw [pow_add, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (degree_nonneg U x) (hdeg x) r)
    (pow_nonneg (degree_nonneg U x) a)

lemma Apart_le (a r : ℕ) : Apart U (a + r) ≤ Δ ^ r * Apart U a := by
  unfold Apart
  rw [← integral_const_mul]
  refine integral_mono ((isBdd_degPow U (a + r)).mul (isBdd_one_sub_row U)).integrable
    (((isBdd_degPow U a).mul (isBdd_one_sub_row U)).smul _).integrable fun x ↦ ?_
  have h0 : 0 ≤ ∫ y, U x y * (1 - U x y) ∂μ :=
    integral_nonneg fun y ↦ mul_nonneg (U.nonneg x y) (by linarith [U.le_one x y])
  simp only []
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (degPow_le hΔ hdeg x a r) h0

omit hΔ hdeg in
lemma Apart_nonneg (a : ℕ) : 0 ≤ Apart U a :=
  integral_nonneg fun x ↦ mul_nonneg (pow_nonneg (degree_nonneg U x) a)
    (integral_nonneg fun y ↦ mul_nonneg (U.nonneg x y) (by linarith [U.le_one x y]))

omit hΔ hdeg in
lemma Res_nonneg (a : ℕ) : 0 ≤ Res U a :=
  sub_nonneg.mpr (tsum_weighted_le U (isBdd_degPow U a) fun x ↦ pow_nonneg (degree_nonneg U x) a)

lemma Res_le (a r : ℕ) : Res U (a + r) ≤ Δ ^ r * Res U a := by
  set w : Ω → ℝ := fun x ↦ Δ ^ r * degree U x ^ a - degree U x ^ (a + r) with hw
  have hwb : IsBdd w := ((isBdd_degPow U a).smul _).sub (isBdd_degPow U (a + r))
  have hw0 : ∀ x, 0 ≤ w x := fun x ↦ sub_nonneg.mpr (degPow_le hΔ hdeg x a r)
  have h := tsum_weighted_le U hwb hw0
  have hsa := summable_weighted U (isBdd_degPow U a) fun x ↦ pow_nonneg (degree_nonneg U x) a
  have hsb := summable_weighted U (isBdd_degPow U (a + r))
    fun x ↦ pow_nonneg (degree_nonneg U x) (a + r)
  have hφ : ∀ i : EIdx U, ∫ x, w x * phi U i x ^ 2 ∂μ =
      Δ ^ r * (∫ x, degree U x ^ a * phi U i x ^ 2 ∂μ) -
        ∫ x, degree U x ^ (a + r) * phi U i x ^ 2 ∂μ := by
    intro i
    rw [← integral_const_mul, ← integral_sub
      ((((isBdd_degPow U a).mul (isBdd_phi U i).sq).smul _).integrable)
      ((isBdd_degPow U (a + r)).mul (isBdd_phi U i).sq).integrable]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by simp only [hw]; ring)
  have hr : ∫ x, w x * rowSq U x ∂μ =
      Δ ^ r * (∫ x, degree U x ^ a * rowSq U x ∂μ) - ∫ x, degree U x ^ (a + r) * rowSq U x ∂μ := by
    rw [← integral_const_mul, ← integral_sub
      ((((isBdd_degPow U a).mul (isBdd_rowSq U)).smul _).integrable)
      ((isBdd_degPow U (a + r)).mul (isBdd_rowSq U)).integrable]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by simp only [hw]; ring)
  simp_rw [hφ] at h
  rw [hr, Summable.tsum_sub (hsa.mul_left _) hsb, tsum_mul_left] at h
  unfold Res
  linarith

/-- The per-eigenvalue comparison ((4.21),
(4.22)), for odd `a = g - 2 = p + 2` (`p` a Lean index). -/
lemma term_cmp {p : ℕ} (hp : Odd p) (r : ℕ) (i : EIdx U) :
    0 ≤ term U i (p + 1) ∧ term U i (p + r + 1) ≤ cmpConst p r * Δ ^ r * term U i (p + 1) := by
  set c := ev U i with hc
  set g := gN U i with hg
  have hgb : IsBdd g := isBdd_gN U i
  have hwb : IsBdd (fun x ↦ g x ^ 2) := hgb.sq
  have hw0 : ∀ x, 0 ≤ g x ^ 2 := fun x ↦ sq_nonneg _
  have hw1 : ∫ x, g x ^ 2 ∂μ = 1 := integral_gN_sq U i
  have habs : |c| ≤ ∫ x, degree U x * g x ^ 2 ∂μ := abs_ev_le U i
  have hmΔ : ∫ x, degree U x * g x ^ 2 ∂μ ≤ Δ := integral_deg_gN_le U hdeg i
  -- `term = c² (∫ d^j g² - c^j)`
  have hterm : ∀ j : ℕ, term U i j =
      c ^ 2 * ((∫ x, degree U x ^ (j + 1) * g x ^ 2 ∂μ) - c ^ (j + 1)) := by
    intro j
    unfold term
    have : ∫ x, degree U x ^ (j + 1) * phi U i x ^ 2 ∂μ =
        c ^ 2 * ∫ x, degree U x ^ (j + 1) * g x ^ 2 ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp only []
      rw [phi_eq_gN U i x, ← hc, ← hg]
      ring
    rw [this]
    ring
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hC1 := one_le_cmpConst p r
  have hΔr : 0 ≤ Δ ^ r := pow_nonneg hΔ r
  -- the bracket at the exponents `p + 2` and `p + r + 2`
  set Ia := ∫ x, degree U x ^ (p + 2) * g x ^ 2 ∂μ with hIa
  set Ib := ∫ x, degree U x ^ (p + r + 2) * g x ^ 2 ∂μ with hIb
  have hIa0 : 0 ≤ Ia := integral_nonneg fun x ↦ mul_nonneg (pow_nonneg (degree_nonneg U x) _)
    (hw0 x)
  have hIba : Ib ≤ Δ ^ r * Ia := by
    rw [hIb, hIa, ← integral_const_mul]
    refine integral_mono ((isBdd_degPow U _).mul hwb).integrable
      (((isBdd_degPow U _).mul hwb).smul _).integrable fun x ↦ ?_
    simp only []
    rw [show p + r + 2 = (p + 2) + r by ring, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (degPow_le hΔ hdeg x (p + 2) r) (hw0 x)
  have hbr : 0 ≤ Ia - c ^ (p + 2) ∧ Ib - c ^ (p + r + 2) ≤ cmpConst p r * Δ ^ r * (Ia - c ^ (p + 2)) := by
    rcases le_or_gt 0 c with hc0 | hc0
    · have hα : c ≤ ∫ x, degree U x * g x ^ 2 ∂μ := (le_abs_self c).trans habs
      refine ⟨sub_nonneg.mpr ?_, ?_⟩
      · exact jensen_pow (isBdd_degree U) hwb hw0 hw1 (degree_nonneg U) hc0 hα (p + 1)
      · exact scalar_moment (isBdd_degree U) hwb hw0 hw1 hΔ (degree_nonneg U) hdeg hc0 hα p r
    · -- negative eigenvalue: `c^{p+2} = -|c|^{p+2}` since `p + 2` is odd
      have hodd : Odd (p + 2) := hp.add_even even_two
      have hca : c ^ (p + 2) = -|c| ^ (p + 2) := by
        rw [abs_of_neg hc0, hodd.neg_pow, neg_neg]
      have hcΔ : |c| ≤ Δ := habs.trans hmΔ
      have hb : -c ^ (p + r + 2) ≤ Δ ^ r * |c| ^ (p + 2) := by
        calc -c ^ (p + r + 2) ≤ |c ^ (p + r + 2)| := neg_le_abs _
          _ = |c| ^ (p + 2) * |c| ^ r := by rw [abs_pow, show p + r + 2 = (p + 2) + r by ring,
              pow_add]
          _ ≤ |c| ^ (p + 2) * Δ ^ r :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg c) hcΔ r)
                (pow_nonneg (abs_nonneg c) _)
          _ = Δ ^ r * |c| ^ (p + 2) := mul_comm _ _
      have hpos : 0 ≤ Ia - c ^ (p + 2) := by
        rw [hca]; linarith [pow_nonneg (abs_nonneg c) (p + 2)]
      refine ⟨hpos, ?_⟩
      calc Ib - c ^ (p + r + 2) ≤ Δ ^ r * (Ia - c ^ (p + 2)) := by rw [hca]; linarith
        _ ≤ cmpConst p r * Δ ^ r * (Ia - c ^ (p + 2)) := by
          rw [mul_assoc]
          exact le_mul_of_one_le_left (mul_nonneg hΔr hpos) hC1
  obtain ⟨hb0, hb1⟩ := hbr
  rw [hterm (p + 1), hterm (p + r + 1)]
  refine ⟨mul_nonneg hc2 hb0, ?_⟩
  have := mul_le_mul_of_nonneg_left hb1 hc2
  calc c ^ 2 * ((∫ x, degree U x ^ (p + r + 1 + 1) * g x ^ 2 ∂μ) - c ^ (p + r + 1 + 1))
      = c ^ 2 * (Ib - c ^ (p + r + 2)) := rfl
    _ ≤ c ^ 2 * (cmpConst p r * Δ ^ r * (Ia - c ^ (p + 2))) := this
    _ = cmpConst p r * Δ ^ r * (c ^ 2 * ((∫ x, degree U x ^ (p + 1 + 1) * g x ^ 2 ∂μ) -
        c ^ (p + 1 + 1))) := by rw [hIa]; ring

/-- **Theorem 4.7.** For odd `g ≥ 5` and `s = g + r ≥ g`, written
`g = p + 4` (`p` an odd natural-number index, not the edge density):
`0 ≤ S_g(U)` and `S_s(U) ≤ ((s-2)(s-3))/((g-2)(g-3)) Δ^{s-g} S_g(U)`. -/
theorem cycle_comparison {p : ℕ} (hp : Odd p) (r : ℕ) :
    0 ≤ Ss U (p + 4) ∧ Ss U (p + r + 4) ≤ cmpConst p r * Δ ^ r * Ss U (p + 4) := by
  have hda := Ss_decomp U (p + 1)
  have hdb := Ss_decomp U (p + r + 1)
  have hA := Apart_le hΔ hdeg (p + 2) r
  have hA0 := Apart_nonneg (U := U) (p + 2)
  have hR := Res_le hΔ hdeg (p + 2) r
  have hR0 := Res_nonneg (U := U) (p + 2)
  have hT0 : 0 ≤ ∑' i : EIdx U, term U i (p + 1) :=
    tsum_nonneg fun i ↦ (term_cmp hΔ hdeg hp r i).1
  have hT : ∑' i : EIdx U, term U i (p + r + 1) ≤
      cmpConst p r * Δ ^ r * ∑' i : EIdx U, term U i (p + 1) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun i ↦ (term_cmp hΔ hdeg hp r i).2) (summable_term U _)
      ((summable_term U _).mul_left _)
  have hC1 := one_le_cmpConst p r
  have hΔr : 0 ≤ Δ ^ r := pow_nonneg hΔ r
  have e1 : p + 1 + 3 = p + 4 := rfl
  have e2 : p + r + 1 + 3 = p + r + 4 := rfl
  have e3 : p + 1 + 1 = p + 2 := rfl
  have e4 : p + r + 1 + 1 = p + 2 + r := by ring
  rw [e1, e3] at hda
  rw [e2, e4] at hdb
  have hS0 : 0 ≤ Ss U (p + 4) := by rw [hda]; linarith
  refine ⟨hS0, ?_⟩
  have hAR : Δ ^ r * (Apart U (p + 2) + Res U (p + 2)) ≤
      cmpConst p r * Δ ^ r * (Apart U (p + 2) + Res U (p + 2)) := by
    rw [mul_assoc]
    exact le_mul_of_one_le_left (mul_nonneg hΔr (add_nonneg hA0 hR0)) hC1
  rw [hdb, hda]
  nlinarith

end Compare

end Spectral

end Taeyoung.Paper.Eventual
