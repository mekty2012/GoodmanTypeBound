import Taeyoung.Paper.TargetPolynomial
import Taeyoung.Methods.BaseCone
import Taeyoung.Methods.Link.ConeChromatic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Universal vertices (`paper.pdf`, Section 3, Proposition 3.2)

**Proposition.** Let `F` have `n ≥ 2` vertices, and let `φ = Φ_F` satisfy
`φ, φ', φ'' ≥ 0` on `[a,1]` and `φ(a) = 0`, where `0 ≤ a < 1`.  If
`t(F,V) ≥ φ(z)` for every graphon `V` of edge density `z > a`, then `K₁ ∨ F`
satisfies `t(K₁ ∨ F, W) ≥ Φ_{K₁∨F}(p)` for `p > b := 1/(2-a)`, and
`Φ_{K₁∨F}` again has the three sign properties on `[b,1]`, with
`Φ_{K₁∨F}(b) = 0`.

This is `lifting`, which proves the bound on the closed range `p ≥ b` and needs
only `a < 1`.  The analytic core — conditioning on the apex, the tangent
line of `φ` at `c = 2 - 1/p`, and the weighted rooted-triangle inequality — is
already `Methods/BaseCone.lean` (`coneGraph_pow_bound`).  What is new here is the
calculus: the tangent-line inequality from `φ'' ≥ 0` (`tangent_of_deriv2_nonneg`),
the cone identity `Φ_{K₁∨F}(p) = p^n Φ_F(2 - 1/p)` (`eval_targetPoly_cone`), and
the computation of the first two derivatives of `p ↦ p^n φ(2 - 1/p)`, which
shows that the sign properties propagate.

`iterated_lifting` iterates the proposition `s` times: under the hypotheses,
`K_s ∨ F` satisfies the bound for `p ≥ 1 - 1/(s + 1/(1-a))`, the closed form of
(3.3) (which has `p >`).
-/

open MeasureTheory Polynomial Finset Filter Topology

namespace Taeyoung.Paper

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link

/-! ### The sign profile carried by the induction -/

/-- The hypotheses on `φ = Φ_F` in the lifting proposition: `φ(a) = 0`, and
`φ, φ', φ'' ≥ 0` on `[a,1]`. -/
structure TargetProfile (φ : ℝ[X]) (a : ℝ) : Prop where
  eval_eq_zero : φ.eval a = 0
  nonneg : ∀ z, a ≤ z → z ≤ 1 → 0 ≤ φ.eval z
  deriv_nonneg : ∀ z, a ≤ z → z ≤ 1 → 0 ≤ φ.derivative.eval z
  deriv2_nonneg : ∀ z, a ≤ z → z ≤ 1 → 0 ≤ φ.derivative.derivative.eval z

/-- **The tangent line of a polynomial with `φ'' ≥ 0` on `[a,b]` lies below it
there.** -/
theorem tangent_of_deriv2_nonneg {φ : ℝ[X]} {a b : ℝ}
    (h2 : ∀ z, a ≤ z → z ≤ b → 0 ≤ φ.derivative.derivative.eval z)
    {c w : ℝ} (hca : a ≤ c) (hcb : c ≤ b) (hwa : a ≤ w) (hwb : w ≤ b) :
    φ.eval c + φ.derivative.eval c * (w - c) ≤ φ.eval w := by
  -- `φ'` is monotone on `[a,b]`
  have hmono : MonotoneOn (fun z ↦ φ.derivative.eval z) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      φ.derivative.continuous.continuousOn φ.derivative.differentiable.differentiableOn
      fun x hx ↦ ?_
    rw [interior_Icc] at hx
    rw [Polynomial.deriv]
    exact h2 x hx.1.le hx.2.le
  rcases lt_trichotomy c w with hcw | hcw | hcw
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope (fun z ↦ φ.eval z) hcw
      φ.continuous.continuousOn φ.differentiable.differentiableOn
    rw [Polynomial.deriv] at hξeq
    have hle : φ.derivative.eval c ≤ φ.derivative.eval ξ :=
      hmono ⟨hca, hcb⟩ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩ hξ.1.le
    rw [hξeq, le_div_iff₀ (by linarith)] at hle
    linarith
  · subst hcw; simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope (fun z ↦ φ.eval z) hcw
      φ.continuous.continuousOn φ.differentiable.differentiableOn
    rw [Polynomial.deriv] at hξeq
    have hle : φ.derivative.eval ξ ≤ φ.derivative.eval c :=
      hmono ⟨by linarith [hξ.1], by linarith [hξ.2]⟩ ⟨hca, hcb⟩ hξ.2.le
    rw [hξeq, div_le_iff₀ (by linarith)] at hle
    nlinarith

/-! ### The cone identity -/

/-- **`Φ_{K₁∨F}(p) = p^n Φ_F(2 - 1/p)`** at the level of target polynomials, for
every `p > 0`.  The hypotheses are those of a chromatic polynomial on `n` vertices
and of the cone's polynomial `X·P(X-1)` on `n + 1`. -/
theorem eval_targetPoly_cone {n : ℕ} {P : ℝ[X]} (hdeg : P.natDegree ≤ n)
    (hcoef : P.coeff n = 1) (hdeg' : (X * P.comp (X - 1)).natDegree ≤ n + 1)
    (hcoef' : (X * P.comp (X - 1)).coeff (n + 1) = 1) {p : ℝ} (hp : 0 < p) :
    (targetPoly (n + 1) (X * P.comp (X - 1))).eval p =
      p ^ n * (targetPoly n P).eval (2 - p⁻¹) := by
  by_cases hp1 : p = 1
  · subst hp1
    rw [eval_targetPoly_one, hcoef', show (2 : ℝ) - 1⁻¹ = 1 by norm_num,
      eval_targetPoly_one, hcoef, one_pow, one_mul]
  · have hc1 : (2 : ℝ) - p⁻¹ ≠ 1 := by
      intro h
      apply hp1
      have : p⁻¹ = 1 := by linarith
      rw [inv_eq_one] at this
      exact this
    have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
    rw [eval_targetPoly_of_ne_one hdeg' hp1, eval_targetPoly_of_ne_one hdeg hc1,
      eval_mul, eval_X, eval_comp, eval_sub, eval_X, eval_one]
    have h1 : 1 / (1 - p) - 1 = p / (1 - p) := by field_simp; ring
    have h2 : 1 / (1 - (2 - p⁻¹)) = p / (1 - p) := by
      have : 1 - (2 - p⁻¹) = (1 - p) / p := by field_simp; ring
      rw [this, one_div_div]
    have h3 : 1 - (2 - p⁻¹) = (1 - p) / p := by field_simp; ring
    rw [h1, h2, h3, div_pow, pow_succ]
    field_simp

/-! ### Derivatives of `p ↦ p^m φ(2 - 1/p)` -/

/-- One differentiation of `x ↦ x^m φ(2 - x⁻¹)`. -/
lemma hasDerivAt_liftFun (m : ℕ) (φ : ℝ[X]) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y ↦ y ^ m * φ.eval (2 - y⁻¹))
      (m * x ^ (m - 1) * φ.eval (2 - x⁻¹) +
        x ^ m * (φ.derivative.eval (2 - x⁻¹) * (x ^ 2)⁻¹)) x := by
  have hg : HasDerivAt (fun y : ℝ ↦ 2 - y⁻¹) ((x ^ 2)⁻¹) x :=
    ((hasDerivAt_inv hx).const_sub 2).congr_deriv (by ring)
  have hφ' : HasDerivAt (fun z ↦ φ.eval z) (φ.derivative.eval (2 - x⁻¹)) (2 - x⁻¹) :=
    φ.hasDerivAt (2 - x⁻¹)
  have hcomp : HasDerivAt (fun y ↦ φ.eval (2 - y⁻¹))
      (φ.derivative.eval (2 - x⁻¹) * (x ^ 2)⁻¹) x :=
    HasDerivAt.comp (h := fun y : ℝ ↦ 2 - y⁻¹) x hφ' hg
  exact (hasDerivAt_pow m x).mul hcomp

/-! ### The lifting proposition -/

variable {h : ℕ}

/-- The cone polynomial `X·P(X-1)` of a chromatic polynomial `P` of `F` is a
chromatic polynomial of `K₁ ∨ F`; record the two degree facts it inherits. -/
lemma cone_degree_facts (F : SimpleGraph (Fin (h + 2))) [DecidableRel F.Adj]
    {P : ℝ[X]} (hP : IsChromaticPolynomial F P) :
    (X * P.comp (X - 1)).natDegree ≤ h + 2 + 1 ∧
      (X * P.comp (X - 1)).coeff (h + 2 + 1) = 1 := by
  have hc := isChromaticPolynomial_coneGraph F hP
  have h1 := hc.natDegree_le
  have h2 := hc.coeff_card
  simp only [Fintype.card_fin] at h1 h2
  exact ⟨h1, h2⟩

/-- `lifting` for a base indexed by `Fin (h + 2)`. -/
theorem lifting_aux (F : SimpleGraph (Fin (h + 2))) [DecidableRel F.Adj]
    {P : ℝ[X]} (hP : IsChromaticPolynomial F P) {a : ℝ} (ha1 : a < 1)
    (hprof : TargetProfile (targetPoly (h + 2) P) a)
    (hbase : SatisfiesLowerBoundOn F (Set.Ioi a)) :
    SatisfiesLowerBoundOn (coneGraph F) (Set.Ici (1 / (2 - a))) ∧
      TargetProfile (targetPoly (h + 2 + 1) (X * P.comp (X - 1))) (1 / (2 - a)) := by
  set φ := targetPoly (h + 2) P with hφ
  set ψ := targetPoly (h + 2 + 1) (X * P.comp (X - 1)) with hψ
  have hdeg : P.natDegree ≤ h + 2 := by simpa using hP.natDegree_le
  have hcoef : P.coeff (h + 2) = 1 := by simpa using hP.coeff_card
  obtain ⟨hdeg', hcoef'⟩ := cone_degree_facts F hP
  have h2a : 0 < 2 - a := by linarith
  set b := 1 / (2 - a) with hb
  have hbpos : 0 < b := by positivity
  have hb1 : b ≤ 1 := by rw [hb, div_le_one h2a]; linarith
  -- `c = 2 - 1/p` lies in `[a,1]` exactly when `p ∈ [b,1]`
  have hc_mem : ∀ p, b ≤ p → p ≤ 1 → a ≤ 2 - p⁻¹ ∧ 2 - p⁻¹ ≤ 1 := by
    intro p hbp hp1
    have hp0 : 0 < p := lt_of_lt_of_le hbpos hbp
    constructor
    · have : p⁻¹ ≤ 2 - a := by
        rw [inv_le_comm₀ hp0 h2a]
        simpa [hb, one_div] using hbp
      linarith
    · have : 1 ≤ p⁻¹ := one_le_inv₀ hp0 |>.mpr hp1
      linarith
  have hψeval : ∀ x, 0 < x → ψ.eval x = x ^ (h + 2) * φ.eval (2 - x⁻¹) :=
    fun x hx ↦ eval_targetPoly_cone hdeg hcoef hdeg' hcoef' hx
  -- the base bound, closed at `a`
  have hbase' : ∀ {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
      [IsProbabilityMeasure ν] (V : Graphon Ω' ν),
      a ≤ cliqueDensity 2 V → φ.eval (cliqueDensity 2 V) ≤ homDensity F V := by
    intro Ω' _ ν _ V hV
    rcases eq_or_lt_of_le hV with heq | hlt
    · rw [← heq, hprof.eval_eq_zero]; exact homDensity_nonneg F V
    · have := hbase P hP V hlt
      rw [chromaticTarget_eq_eval_targetPoly hP] at this
      simp only [Fintype.card_fin] at this
      exact this
  refine ⟨?_, ?_⟩
  · -- the density bound
    intro Q hQ Ω _ μ _ W hW
    have hQeq : Q = X * P.comp (X - 1) :=
      IsChromaticPolynomial.unique _ hQ (isChromaticPolynomial_coneGraph F hP)
    subst hQeq
    set p := edgeDensity W with hpdef
    have hbp : b ≤ p := hW
    have hp1 : p ≤ 1 := cliqueDensity_le_one 2 W
    have hp0 : 0 < p := lt_of_lt_of_le hbpos hbp
    obtain ⟨hca, hc1⟩ := hc_mem p hbp hp1
    have hkey := BaseCone.coneGraph_pow_bound F W (φ := fun z ↦ φ.eval z) (a := a)
      (lam := φ.derivative.eval (2 - 1 / p)) hprof.eval_eq_zero
      (hprof.deriv_nonneg _ (by rwa [one_div]) (by rwa [one_div])) ha1.le hp0
      (fun w hwa hw1 ↦ tangent_of_deriv2_nonneg hprof.deriv2_nonneg
        (by rwa [one_div]) (by rwa [one_div]) hwa hw1)
      (hprof.nonneg _ (by rwa [one_div]) (by rwa [one_div])) hbase'
    rw [chromaticTarget_eq_eval_targetPoly (isChromaticPolynomial_coneGraph F hP)]
    simp only [Fintype.card_fin]
    rw [← hψ, hψeval p hp0, ← one_div]
    exact hkey
  · -- the profile of `ψ` at `b`
    -- first and second derivatives of `ψ` on `(0, ∞)`
    have hψ1 : ∀ x, 0 < x → ψ.derivative.eval x =
        ((h + 2 : ℕ) : ℝ) * x ^ (h + 1) * φ.eval (2 - x⁻¹) +
          x ^ h * φ.derivative.eval (2 - x⁻¹) := by
      intro x hx
      have hd := hasDerivAt_liftFun (h + 2) φ hx.ne'
      have hev : (fun y ↦ ψ.eval y) =ᶠ[𝓝 x] fun y ↦ y ^ (h + 2) * φ.eval (2 - y⁻¹) :=
        eventually_of_mem (Ioi_mem_nhds hx) fun y hy ↦ hψeval y hy
      have hψd := (ψ.hasDerivAt x).congr_of_eventuallyEq hev.symm
      rw [hψd.unique hd]
      have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx.ne'
      rw [show h + 2 - 1 = h + 1 by omega]
      have : x ^ (h + 2) * (x ^ 2)⁻¹ = x ^ h := by
        rw [pow_add, mul_assoc, mul_inv_cancel₀ hx2, mul_one]
      rw [← this]; ring
    have hψ2 : ∀ x, 0 < x → ψ.derivative.derivative.eval x =
        ((h + 2 : ℕ) : ℝ) * (((h + 1 : ℕ) : ℝ) * x ^ (h + 1 - 1) * φ.eval (2 - x⁻¹) +
            x ^ (h + 1) * (φ.derivative.eval (2 - x⁻¹) * (x ^ 2)⁻¹)) +
          ((h : ℝ) * x ^ (h - 1) * φ.derivative.eval (2 - x⁻¹) +
            x ^ h * (φ.derivative.derivative.eval (2 - x⁻¹) * (x ^ 2)⁻¹)) := by
      intro x hx
      have hd := ((hasDerivAt_liftFun (h + 1) φ hx.ne').const_mul ((h + 2 : ℕ) : ℝ)).add
        (hasDerivAt_liftFun h φ.derivative hx.ne')
      have hev : (fun y ↦ ψ.derivative.eval y) =ᶠ[𝓝 x]
          fun y ↦ ((h + 2 : ℕ) : ℝ) * (y ^ (h + 1) * φ.eval (2 - y⁻¹)) +
            y ^ h * φ.derivative.eval (2 - y⁻¹) :=
        eventually_of_mem (Ioi_mem_nhds hx) fun y hy ↦ by
          dsimp only
          rw [hψ1 y hy]; ring
      have hψd := (ψ.derivative.hasDerivAt x).congr_of_eventuallyEq hev.symm
      rw [hψd.unique hd]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hψeval b hbpos]
      have : 2 - b⁻¹ = a := by rw [hb, one_div, inv_inv]; ring
      rw [this, hprof.eval_eq_zero, mul_zero]
    · intro z hbz hz1
      have hz0 : 0 < z := lt_of_lt_of_le hbpos hbz
      obtain ⟨hca, hc1⟩ := hc_mem z hbz hz1
      rw [hψeval z hz0]
      exact mul_nonneg (pow_nonneg hz0.le _) (hprof.nonneg _ hca hc1)
    · intro z hbz hz1
      have hz0 : 0 < z := lt_of_lt_of_le hbpos hbz
      obtain ⟨hca, hc1⟩ := hc_mem z hbz hz1
      rw [hψ1 z hz0]
      have := hprof.nonneg _ hca hc1
      have := hprof.deriv_nonneg _ hca hc1
      positivity
    · intro z hbz hz1
      have hz0 : 0 < z := lt_of_lt_of_le hbpos hbz
      obtain ⟨hca, hc1⟩ := hc_mem z hbz hz1
      rw [hψ2 z hz0]
      have := hprof.nonneg _ hca hc1
      have := hprof.deriv_nonneg _ hca hc1
      have := hprof.deriv2_nonneg _ hca hc1
      positivity

/-- **Proposition 3.2.**  Let `F` have `m ≥ 2` vertices.  Under the
profile hypotheses on `Φ_F` at `a < 1` and the base bound `t(F,V) ≥ Φ_F(z)` for
`z > a`, the cone `K₁ ∨ F` satisfies the Goodman-type inequality for every
`p ≥ b = 1/(2-a)`, and `Φ_{K₁ ∨ F}` has the profile at `b`: it vanishes at `b`
and it and its first two derivatives are nonnegative on `[b,1]`. -/
theorem lifting {m : ℕ} (hm : 2 ≤ m) (F : SimpleGraph (Fin m)) [DecidableRel F.Adj]
    {P : ℝ[X]} (hP : IsChromaticPolynomial F P) {a : ℝ} (ha1 : a < 1)
    (hprof : TargetProfile (targetPoly m P) a)
    (hbase : SatisfiesLowerBoundOn F (Set.Ioi a)) :
    SatisfiesLowerBoundOn (coneGraph F) (Set.Ici (1 / (2 - a))) ∧
      TargetProfile (targetPoly (m + 1) (X * P.comp (X - 1))) (1 / (2 - a)) := by
  obtain ⟨h, rfl⟩ : ∃ h, m = h + 2 := ⟨m - 2, by omega⟩
  exact lifting_aux F hP ha1 hprof hbase

/-! ### Iterating: clique joins `K_s ∨ F` -/

/-- `K_s ∨ F`, as `s` successive cones over `F`. -/
def iterCone {n : ℕ} : (s : ℕ) → SimpleGraph (Fin n) → SimpleGraph (Fin (n + s))
  | 0, F => F
  | s + 1, F => coneGraph (iterCone s F)

/-- The adjacency of an iterated cone is decidable whenever that of the base is. -/
instance iterCone_decidableAdj {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    (s : ℕ) → DecidableRel (iterCone s F).Adj
  | 0 => inferInstanceAs (DecidableRel F.Adj)
  | s + 1 => by
      haveI := iterCone_decidableAdj F s
      exact inferInstanceAs (DecidableRel (coneGraph (iterCone s F)).Adj)

/-- The chromatic polynomial of `K_s ∨ F`: `s` substitutions `P ↦ X·P(X-1)`. -/
noncomputable def iterConePoly (P : ℝ[X]) : ℕ → ℝ[X]
  | 0 => P
  | s + 1 => X * (iterConePoly P s).comp (X - 1)

theorem isChromaticPolynomial_iterCone {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] {P : ℝ[X]} (hP : IsChromaticPolynomial F P) :
    ∀ s, IsChromaticPolynomial (iterCone s F) (iterConePoly P s)
  | 0 => hP
  | s + 1 => isChromaticPolynomial_coneGraph (iterCone s F)
      (isChromaticPolynomial_iterCone F hP s)

theorem isChromaticNumber_iterCone {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] {r : ℕ} (hr : IsChromaticNumber F r) :
    ∀ s, IsChromaticNumber (iterCone s F) (r + s)
  | 0 => hr
  | s + 1 => isChromaticNumber_coneGraph (iterCone s F) (isChromaticNumber_iterCone F hr s)

/-- The iterated threshold `a_s = 1 - 1/(s + 1/(1-a))`. -/
noncomputable def iterThreshold (a : ℝ) (s : ℕ) : ℝ := 1 - 1 / ((s : ℝ) + 1 / (1 - a))

lemma iterThreshold_zero {a : ℝ} (ha1 : a < 1) : iterThreshold a 0 = a := by
  have : 1 - a ≠ 0 := by linarith
  simp [iterThreshold]

lemma iterThreshold_lt_one {a : ℝ} (ha1 : a < 1) (s : ℕ) : iterThreshold a s < 1 := by
  have h1 : 0 < 1 / (1 - a) := by apply one_div_pos.mpr; linarith
  have : 0 < 1 / ((s : ℝ) + 1 / (1 - a)) := by positivity
  unfold iterThreshold; linarith

/-- The thresholds obey `a_{s+1} = 1/(2 - a_s)`. -/
lemma iterThreshold_succ {a : ℝ} (ha1 : a < 1) (s : ℕ) :
    1 / (2 - iterThreshold a s) = iterThreshold a (s + 1) := by
  have h1 : 0 < 1 / (1 - a) := by apply one_div_pos.mpr; linarith
  set c := (s : ℝ) + 1 / (1 - a) with hc
  have hcpos : 0 < c := by positivity
  have hc1 : ((s + 1 : ℕ) : ℝ) + 1 / (1 - a) = c + 1 := by push_cast; ring
  unfold iterThreshold
  rw [← hc, hc1]
  have hc0 : c ≠ 0 := hcpos.ne'
  have hc10 : c + 1 ≠ 0 := by linarith
  have h2 : 2 - (1 - 1 / c) = (c + 1) / c := by field_simp; ring
  rw [h2, one_div_div, eq_sub_iff_add_eq, ← add_div, div_self hc10]

/-- **Iterated lifting (3.3).**  Under the hypotheses of
`lifting`, `K_s ∨ F` satisfies the Goodman-type inequality for
`p ≥ 1 - 1/(s + 1/(1-a))`, and its target keeps the profile there. -/
theorem iterated_lifting {n : ℕ} (hn : 2 ≤ n) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    {P : ℝ[X]} (hP : IsChromaticPolynomial F P) {a : ℝ} (ha1 : a < 1)
    (hprof : TargetProfile (targetPoly n P) a)
    (hbase : SatisfiesLowerBoundOn F (Set.Ioi a)) :
    ∀ s : ℕ, SatisfiesLowerBoundOn (iterCone s F) (Set.Ici (iterThreshold a s)) ∧
      TargetProfile (targetPoly (n + s) (iterConePoly P s)) (iterThreshold a s)
  | 0 => by
      rw [iterThreshold_zero ha1]
      refine ⟨fun Q hQ Ω _ μ _ W hW ↦ ?_, hprof⟩
      rcases eq_or_lt_of_le (show a ≤ edgeDensity W from hW) with heq | hlt
      · rw [chromaticTarget_eq_eval_targetPoly hQ]
        simp only [Fintype.card_fin, Nat.add_zero]
        rw [IsChromaticPolynomial.unique _ hQ hP, ← heq, hprof.eval_eq_zero]
        exact homDensity_nonneg _ W
      · exact hbase Q hQ W hlt
  | s + 1 => by
      obtain ⟨hb, hp⟩ := iterated_lifting hn F hP ha1 hprof hbase s
      have hlift := lifting (by omega : 2 ≤ n + s) (iterCone s F)
        (isChromaticPolynomial_iterCone F hP s) (iterThreshold_lt_one ha1 s) hp
        (hb.mono Set.Ioi_subset_Ici_self)
      rw [iterThreshold_succ ha1] at hlift
      exact hlift

end Taeyoung.Paper
