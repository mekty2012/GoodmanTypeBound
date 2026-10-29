import Taeyoung.Methods.Negative.WeightedStep

/-!
# The five-part graphon `W_ε` (Atlas 152)

`paper.pdf`, Section 5.2, refutes the Goodman-type bound for
Atlas 152 with the step graphon `W_ε` on five classes `A₁, A₂, B, S₁, S₂` of
masses

```
(1/2 - ε)·624/625,  (1/2 - ε)/625,  1/2,  ε/10,  9ε/10
```

and values (rows and columns ordered `A₁, A₂, B, S₁, S₂`)

```
⎛ 0  0  1     1     0 ⎞
⎜ 0  0  1     0     1 ⎟
⎜ 1  1  0     1/16  1 ⎟
⎜ 1  0  1/16  0     0 ⎟
⎝ 0  1  1     0     0 ⎠
```

for every sufficiently small `ε > 0`.  The Lean witness is `W_ε` at `ε = 1/3000`:
the masses over `D = 3750000` are `w = (1870752, 2998, 1875000, 125, 1125)` and
the values over `s = 16` form the matrix `N152`.  Its edge density is
`p = 18750093281/37500000000 > 1/2`; the row `Examples/Graph152.lean` evaluates
`t(H, W_ε)` and compares it with `Φ_H(p)`.
-/

open Finset MeasureTheory

namespace Taeyoung.Methods.Negative

open Taeyoung

def w152 : Fin 5 → ℕ := ![1870752, 2998, 1875000, 125, 1125]

theorem w152_sum : ∑ i, w152 i = 3750000 := by decide

noncomputable instance : IsProbabilityMeasure (weightedMeasure 5 w152 3750000) :=
  isProbabilityMeasure_weightedMeasure 5 w152 3750000 w152_sum (by norm_num)

def N152 : Fin 5 → Fin 5 → ℕ :=
  ![![0, 0, 16, 16, 0], ![0, 0, 16, 0, 16], ![16, 16, 0, 1, 16],
    ![16, 0, 1, 0, 0], ![0, 16, 16, 0, 0]]

theorem N152_symm : ∀ i j, N152 i j = N152 j i := by decide
theorem N152_le : ∀ i j, N152 i j ≤ 16 := by decide

/-- The five-part graphon `W_ε` at `ε = 1/3000`. -/
noncomputable def W152 : Graphon (Fin 5) (weightedMeasure 5 w152 3750000) where
  toFun i j := (N152 i j : ℝ) / (16 : ℝ)
  measurable := measurable_of_finite _
  nonneg i j := by positivity
  le_one i j := by
    rw [div_le_one (by norm_num : (0:ℝ) < 16)]
    exact_mod_cast N152_le i j
  symm i j := by rw [N152_symm i j]

@[simp] lemma W152_apply (i j : Fin 5) : W152 i j = (N152 i j : ℝ) / (16 : ℝ) := rfl

theorem Sp152 :
    ∑ z : Fin 2 → Fin 5, (∏ v, w152 (z v)) * N152 (z 0) (z 1)
      = 112500559686000 := by
  decide +kernel

theorem cliqueDensity_152 :
    cliqueDensity 2 W152 = 18750093281 / 37500000000 := by
  rw [cliqueDensity, homDensity_weighted 5 w152 3750000 (⊤ : SimpleGraph (Fin 2))
    w152_sum (by norm_num) W152 (fun z ↦ N152 (z 0) (z 1)) ((16 : ℝ))
    (fun z ↦ by rw [graphWeight_top_fin_two]; exact W152_apply _ _), Sp152]
  norm_num

end Taeyoung.Methods.Negative
