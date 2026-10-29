import Taeyoung.Paper.OddCycles
import Taeyoung.Paper.Eventual.Double

/-!
# Path and cycle quantities (`paper.pdf`, Lemma 4.6)

For a graphon `U` with degree function `d ≤ Δ`, `q = ∫ d`, `X = ∫ (d-q)²`:

* `pk U n`: the path kernel `U^{∘(n+1)}` with `n + 1` edges (`OddCycleBound.compPow`);
* `Qs U s = ∫∫ U^{∘(s-1)}(a,b) (1 - U(a,b))`, i.e. `t(P_s,U) - t(C_s,U)`;
* `Ss U s = M_{s-1} - t(C_s,U)`, with `M_r = ∫ d^r` (`Mom`).

Proved here:

* `pk_le`: `U^{∘(n+1)} ≤ Δ^n` (4.13);
* `Qs_eq`: `Q_s = t(P_s,U) - t(C_s,U)`;
* `Qs_le_triangle`: **Lemma 4.6**, `Q_s ≤ (s-2) Δ^{s-3} Y` with `Y = Q_3`;
* `pth_variance`, `Mom_variance`: path densities and degree moments are within
  `C(r,2) Δ^{r-2} X` of `q^r` (from `GoodWeight`; Lemma 4.4,
  (4.8) for paths and (4.9)).
-/

open MeasureTheory Finset

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Kernels

variable (U : Graphon Ω μ)

/-- The path kernel `U^{∘(n+1)}` with `n + 1` edges. -/
noncomputable abbrev pk (n : ℕ) : Ω → Ω → ℝ := OddCycleBound.compPow μ U.toFun n

/-- `Q_s = ∫∫ U^{∘(s-1)}(a,b)(1 - U(a,b))`. -/
noncomputable def Qs (s : ℕ) : ℝ := dint μ (fun a b ↦ pk U (s - 2) a b * (1 - U a b))

/-- `M_r = ∫ d^r`. -/
noncomputable def Mom (r : ℕ) : ℝ := ∫ x, degree U x ^ r ∂μ

/-- `t(C_s,U)`. -/
noncomputable def cyc (s : ℕ) : ℝ := OddCycleBound.cycleDensity μ U.toFun s

/-- `t(P,U)` for the path with `r` edges. -/
noncomputable def pth (r : ℕ) : ℝ := OddCycleBound.pathDensity U.toFun μ r

/-- `S_s = M_{s-1} - t(C_s,U)`. -/
noncomputable def Ss (s : ℕ) : ℝ := Mom U (s - 1) - cyc U s

lemma goodK_U : OddCycleBound.GoodK U.toFun :=
  OddCycleBound.goodK_of_isGraphon (Paper.isGraphon_ofFoundation U)

lemma goodK_pk (n : ℕ) : OddCycleBound.GoodK (pk U n) :=
  OddCycleBound.goodK_compPow (goodK_U U) n

lemma bdd2_pk (n : ℕ) : Bdd2 (pk U n) :=
  ⟨(goodK_pk U n).meas, (goodK_pk U n).bdd.choose, (goodK_pk U n).bdd.choose_spec.2⟩

lemma bdd2_one_sub : Bdd2 (fun a b ↦ 1 - U a b) := (Bdd2.const 1).sub (Bdd2.graphon U)

lemma pk_nonneg (n : ℕ) (x y : Ω) : 0 ≤ pk U n x y :=
  OddCycleBound.compPow_nonneg (Paper.isGraphon_ofFoundation U) n x y

lemma pk_succ (n : ℕ) (a b : Ω) : pk U (n + 1) a b = ∫ z, U a z * pk U n z b ∂μ := rfl

/-- **(4.13)**: `U^{∘(n+1)} ≤ Δ^n`. -/
lemma pk_le {Δ : ℝ} (hΔ0 : 0 ≤ Δ) (hdeg : ∀ x, degree U x ≤ Δ) :
    ∀ (n : ℕ) (x y : Ω), pk U n x y ≤ Δ ^ n
  | 0, x, y => by
    show U x y ≤ Δ ^ 0
    rw [pow_zero]; exact U.le_one x y
  | n + 1, x, y => by
    rw [pk_succ]
    have hi : Integrable (fun z ↦ U x z * pk U n z y) μ :=
      ((isBdd_row U x).mul ((bdd2_pk U n).col y)).integrable
    calc ∫ z, U x z * pk U n z y ∂μ ≤ ∫ z, U x z * Δ ^ n ∂μ :=
          integral_mono hi ((isBdd_row U x).integrable.mul_const _)
            fun z ↦ mul_le_mul_of_nonneg_left (pk_le hΔ0 hdeg n z y) (U.nonneg _ _)
      _ = degree U x * Δ ^ n := by rw [integral_mul_const]; rfl
      _ ≤ Δ * Δ ^ n := mul_le_mul_of_nonneg_right (hdeg x) (pow_nonneg hΔ0 _)
      _ = Δ ^ (n + 1) := by ring

lemma Qs_nonneg (s : ℕ) : 0 ≤ Qs U s :=
  dint_nonneg fun a b ↦ mul_nonneg (pk_nonneg U _ a b) (by linarith [U.le_one a b])

/-- `Q_s = t(P_s,U) - t(C_s,U)`. -/
theorem Qs_eq (n : ℕ) : Qs U (n + 2) = pth U (n + 1) - cyc U (n + 2) := by
  have hK := bdd2_pk U n
  have hKU := hK.mul (Bdd2.graphon U)
  have h1 : Qs U (n + 2) = dint μ (pk U n) - dint μ (fun a b ↦ pk U n a b * U a b) := by
    unfold Qs
    simp only [Nat.add_sub_cancel]
    rw [← dint_sub hK hKU]
    congr 1; funext a b; ring
  have h2 : dint μ (pk U n) = pth U (n + 1) :=
    OddCycleBound.doubleMean_compPow (Paper.isGraphon_ofFoundation U) n
  have h3 : dint μ (fun a b ↦ pk U n a b * U a b) = cyc U (n + 2) := by
    rw [dint_swap hKU]
    unfold cyc OddCycleBound.cycleDensity OddCycleBound.trace
    refine integral_congr_ae (ae_of_all _ fun b ↦ ?_)
    show _ = ∫ z, U b z * pk U n z b ∂μ
    refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
    simp only []
    rw [U.symm a b]; ring
  rw [h1, h2, h3]

/-- `Q_s - S_s = t(P_s,U) - M_{s-1}`. -/
lemma Qs_sub_Ss (n : ℕ) : Qs U (n + 2) - Ss U (n + 2) = pth U (n + 1) - Mom U (n + 1) := by
  rw [Qs_eq, Ss]
  simp only [show n + 2 - 1 = n + 1 by omega]
  ring

/-- **Lemma 4.6**, one step: `Q_{n+3} ≤ Δ Q_{n+2} + Δ^n Y`. -/
theorem Qs_succ_le {Δ : ℝ} (hΔ0 : 0 ≤ Δ) (hdeg : ∀ x, degree U x ≤ Δ) (n : ℕ) :
    Qs U (n + 3) ≤ Δ * Qs U (n + 2) + Δ ^ n * Qs U 3 := by
  have hK := bdd2_pk U n
  have hU := Bdd2.graphon U
  have h1U := bdd2_one_sub U
  obtain ⟨CK, hCK⟩ := hK.2
  -- the three kernels
  set A : Ω → Ω → ℝ := fun a b ↦ pk U (n + 1) a b * (1 - U a b) with hA
  set B : Ω → Ω → ℝ := fun a b ↦ ∫ z, U a z * pk U n z b * (1 - U z b) ∂μ with hB
  set C : Ω → Ω → ℝ := fun a b ↦ pk U 1 a b * (1 - U a b) with hC
  have hAb : Bdd2 A := (bdd2_pk U (n + 1)).mul h1U
  have hCb : Bdd2 C := (bdd2_pk U 1).mul h1U
  have hGmeas : Measurable fun p : (Ω × Ω) × Ω ↦ U p.1.1 p.2 * pk U n p.2 p.1.2 *
      (1 - U p.2 p.1.2) :=
    ((U.measurable.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hK.1.comp (measurable_snd.prodMk measurable_fst.snd))).mul
      (measurable_const.sub (U.measurable.comp (measurable_snd.prodMk measurable_fst.snd)))
  have hBb : Bdd2 B := by
    refine Bdd2.of_integral hGmeas (1 * CK * 1) fun a b z ↦ ?_
    rw [abs_mul, abs_mul]
    refine mul_le_mul (mul_le_mul ?_ (hCK z b) (abs_nonneg _) zero_le_one) ?_ (abs_nonneg _)
      (mul_nonneg zero_le_one ((abs_nonneg _).trans (hCK z b)))
    · rw [abs_of_nonneg (U.nonneg _ _)]; exact U.le_one _ _
    · rw [abs_le]; constructor <;> linarith [U.nonneg z b, U.le_one z b]
  -- the pointwise splitting
  have hsplit : ∀ a b z, U a z * pk U n z b * (1 - U a b) ≤
      U a z * pk U n z b * (1 - U z b) + Δ ^ n * (U a z * U z b * (1 - U a b)) := by
    intro a b z
    have h1 : 0 ≤ U a z * pk U n z b := mul_nonneg (U.nonneg _ _) (pk_nonneg U n z b)
    have h2 : pk U n z b ≤ Δ ^ n := pk_le U hΔ0 hdeg n z b
    have h3 := U.nonneg a b
    have h4 := U.le_one a b
    have h5 := U.nonneg z b
    have h6 := U.le_one z b
    have h7 := U.nonneg a z
    have h8 : 0 ≤ U z b * (1 - U a b) := mul_nonneg h5 (by linarith)
    have : 1 - U a b ≤ (1 - U z b) + U z b * (1 - U a b) := by nlinarith
    calc U a z * pk U n z b * (1 - U a b)
        ≤ U a z * pk U n z b * ((1 - U z b) + U z b * (1 - U a b)) :=
          mul_le_mul_of_nonneg_left this h1
      _ = U a z * pk U n z b * (1 - U z b) + U a z * pk U n z b * (U z b * (1 - U a b)) := by
          ring
      _ ≤ U a z * pk U n z b * (1 - U z b) + U a z * Δ ^ n * (U z b * (1 - U a b)) := by
          have : U a z * pk U n z b ≤ U a z * Δ ^ n := mul_le_mul_of_nonneg_left h2 h7
          nlinarith
      _ = _ := by ring
  -- integrate the splitting over the middle vertex
  have hpt : ∀ a b, A a b ≤ B a b + Δ ^ n * C a b := by
    intro a b
    have hi0 : Integrable (fun z ↦ U a z * pk U n z b) μ := ((isBdd_row U a).mul (hK.col b)).integrable
    have hi1 : Integrable (fun z ↦ U a z * pk U n z b * (1 - U z b)) μ :=
      ((isBdd_row U a).mul (hK.col b)).mul (h1U.col b) |>.integrable
    have hi2 : Integrable (fun z ↦ U a z * U z b) μ := ((isBdd_row U a).mul (hU.col b)).integrable
    have hA' : A a b = ∫ z, U a z * pk U n z b * (1 - U a b) ∂μ := by
      rw [hA]; simp only []; rw [pk_succ, integral_mul_const]
    have hC' : C a b = ∫ z, U a z * U z b * (1 - U a b) ∂μ := by
      rw [hC]; simp only []; rw [pk_succ, integral_mul_const]; rfl
    rw [hA', hB, hC']
    simp only []
    rw [← integral_const_mul, ← integral_add hi1 ((hi2.mul_const _).const_mul _)]
    exact integral_mono (hi0.mul_const _) (hi1.add ((hi2.mul_const _).const_mul _)) (hsplit a b)
  have hstep1 : Qs U (n + 3) ≤ dint μ B + Δ ^ n * Qs U 3 := by
    have : Qs U (n + 3) = dint μ A := by unfold Qs; rfl
    rw [this]
    have hQ3 : Qs U 3 = dint μ C := by unfold Qs; rfl
    rw [hQ3, ← dint_smul, ← dint_add hBb (Bdd2.smul _ hCb)]
    exact dint_mono hAb (hBb.add (Bdd2.smul _ hCb)) hpt
  -- the first term: integrate the first vertex
  set h : Ω → ℝ := fun z ↦ ∫ b, pk U n z b * (1 - U z b) ∂μ with hh
  have hhb : IsBdd h := (hK.mul h1U).inner
  have hh0 : ∀ z, 0 ≤ h z := fun z ↦ integral_nonneg fun b ↦
    mul_nonneg (pk_nonneg U n z b) (by linarith [U.le_one z b])
  have hBint : dint μ B = ∫ a, kernelApply U h a ∂μ := by
    unfold dint kernelApply
    refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
    have hFa : Bdd2 (fun b z ↦ U a z * pk U n z b * (1 - U z b)) :=
      ((Bdd2.right (isBdd_row U a)).mul hK.swap).mul h1U.swap
    show ∫ b, ∫ z, U a z * pk U n z b * (1 - U z b) ∂μ ∂μ = ∫ z, U a z * h z ∂μ
    rw [integral_integral_swap hFa.integrable_prod]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [hh]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun b ↦ ?_)
    simp only []
    ring
  have hstep2 : dint μ B ≤ Δ * Qs U (n + 2) := by
    rw [hBint, integral_kernelApply U hhb]
    have hQ : Qs U (n + 2) = ∫ z, h z ∂μ := by
      unfold Qs dint; simp only [Nat.add_sub_cancel]; rfl
    rw [hQ, ← integral_const_mul]
    exact integral_mono ((isBdd_degree U).mul hhb).integrable (hhb.integrable.const_mul _)
      fun z ↦ mul_le_mul_of_nonneg_right (hdeg z) (hh0 z)
  linarith

/-- **Lemma 4.6**: `Q_s ≤ (s-2) Δ^{s-3} Y` for `s ≥ 3`. -/
theorem Qs_le_triangle {Δ : ℝ} (hΔ0 : 0 ≤ Δ) (hdeg : ∀ x, degree U x ≤ Δ) :
    ∀ n : ℕ, Qs U (n + 3) ≤ (n + 1) * Δ ^ n * Qs U 3
  | 0 => by simp
  | n + 1 => by
    have h1 := Qs_succ_le U hΔ0 hdeg (n + 1)
    have h2 := Qs_le_triangle hΔ0 hdeg n
    have hQ3 := Qs_nonneg U 3
    calc Qs U (n + 1 + 3) ≤ Δ * Qs U (n + 1 + 2) + Δ ^ (n + 1) * Qs U 3 := h1
      _ ≤ Δ * ((n + 1) * Δ ^ n * Qs U 3) + Δ ^ (n + 1) * Qs U 3 := by
          gcongr
      _ = ((n + 1 : ℕ) + 1 : ℝ) * Δ ^ (n + 1) * Qs U 3 := by push_cast; ring

/-! ### Path densities and degree moments -/

/-- The walk functions `w_j = U^j 1` as vertex weights. -/
noncomputable def pathW : ℕ → BddFun Ω
  | 0 => BddFun.one
  | j + 1 => BddFun.one.mul (BddFun.apply U (pathW j))

lemma pathW_apply : ∀ (j : ℕ) (x : Ω), pathW U j x = OddCycleBound.pathIter U.toFun μ j x
  | 0, x => rfl
  | j + 1, x => by
    show 1 * ∫ z, U x z * pathW U j z ∂μ = ∫ z, U x z * OddCycleBound.pathIter U.toFun μ j z ∂μ
    rw [one_mul]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [pathW_apply j z]

lemma goodWeight_pathW {Δ : ℝ} (hΔ : 0 < Δ) (hdeg : ∀ x, degree U x ≤ Δ) :
    ∀ j, GoodWeight U Δ j (pathW U j)
  | 0 => goodWeight_one U Δ
  | j + 1 => by
    have := (goodWeight_one U Δ).step hΔ hdeg (goodWeight_pathW hΔ hdeg j)
    rw [Nat.zero_add] at this
    exact this

/-- **Path densities**: `Δ² |t(P,U) - q^r| ≤ C(r,2) Δ^r X` for the path with `r` edges. -/
theorem pth_variance {Δ : ℝ} (hΔ : 0 < Δ) (hdeg : ∀ x, degree U x ≤ Δ) (r : ℕ) :
    Δ ^ 2 * |pth U r - meanDeg U ^ r| ≤ (r.choose 2 : ℝ) * Δ ^ r * degVar U := by
  have h := (goodWeight_pathW U hΔ hdeg r).mean_le
  have : pth U r = ∫ y, pathW U r y ∂μ := by
    unfold pth OddCycleBound.pathDensity OddCycleBound.mean
    exact integral_congr_ae (ae_of_all _ fun y ↦ (pathW_apply U r y).symm)
  rw [this]; exact h

/-- The degree powers as vertex weights. -/
noncomputable def powW : ℕ → BddFun Ω
  | 0 => BddFun.one
  | r + 1 => (powW r).mul (BddFun.apply U BddFun.one)

lemma powW_apply : ∀ (r : ℕ) (x : Ω), powW U r x = degree U x ^ r
  | 0, x => by simp [powW, BddFun.one]
  | r + 1, x => by
    show powW U r x * ∫ z, U x z * 1 ∂μ = _
    rw [powW_apply r x, pow_succ]
    simp [degree]

lemma goodWeight_powW {Δ : ℝ} (hΔ : 0 < Δ) (hdeg : ∀ x, degree U x ≤ Δ) :
    ∀ r, GoodWeight U Δ r (powW U r)
  | 0 => goodWeight_one U Δ
  | r + 1 => (goodWeight_powW hΔ hdeg r).step hΔ hdeg (goodWeight_one U Δ)

/-- **Degree moments**: `Δ² |M_r - q^r| ≤ C(r,2) Δ^r X`. -/
theorem Mom_variance {Δ : ℝ} (hΔ : 0 < Δ) (hdeg : ∀ x, degree U x ≤ Δ) (r : ℕ) :
    Δ ^ 2 * |Mom U r - meanDeg U ^ r| ≤ (r.choose 2 : ℝ) * Δ ^ r * degVar U := by
  have h := (goodWeight_powW U hΔ hdeg r).mean_le
  have : Mom U r = ∫ y, powW U r y ∂μ :=
    integral_congr_ae (ae_of_all _ fun y ↦ (powW_apply U r y).symm)
  rw [this]; exact h

/-- `Δ² |Q_s - S_s| ≤ (s-1)(s-2) Δ^{s-1} X`. -/
theorem abs_Qs_sub_Ss_le {Δ : ℝ} (hΔ : 0 < Δ) (hdeg : ∀ x, degree U x ≤ Δ) (n : ℕ) :
    Δ ^ 2 * |Qs U (n + 2) - Ss U (n + 2)| ≤
      2 * ((n + 1).choose 2 : ℝ) * Δ ^ (n + 1) * degVar U := by
  rw [Qs_sub_Ss]
  have h1 := pth_variance U hΔ hdeg (n + 1)
  have h2 := Mom_variance U hΔ hdeg (n + 1)
  have htri : |pth U (n + 1) - Mom U (n + 1)| ≤
      |pth U (n + 1) - meanDeg U ^ (n + 1)| + |Mom U (n + 1) - meanDeg U ^ (n + 1)| := by
    rw [show pth U (n + 1) - Mom U (n + 1) = (pth U (n + 1) - meanDeg U ^ (n + 1)) -
      (Mom U (n + 1) - meanDeg U ^ (n + 1)) by ring]
    exact abs_sub _ _
  nlinarith [sq_nonneg Δ]

end Kernels

end Taeyoung.Paper.Eventual
