import Taeyoung.Methods.Negative.WeightedStep

/-!
# Two perturbations of `T₃` at edge density `2/3`

`paper.pdf`, Section 5.2, gives two step graphons of edge
density exactly `2/3` that beat `T₃`:

* **The four-part graphon** (Atlas 48, 50, 140, 141, 143, 158).  A class `A₁` of
  mass `δ = 1/2000` is added to `T₃`, whose classes `A₂, A₃, A₄` have mass
  `(1-δ)/3` each.  The values are

  ```
  ⎛ 0      1   23/50  23/50 ⎞
  ⎜ 1      ε     1      1   ⎟
  ⎜ 23/50  1     ε      1   ⎟
  ⎝ 23/50  1     1      ε   ⎠
  ```

  with `ε = 8046/99900025`, the value making the edge density `2/3`.
* **The three-part graphon** (Atlas 159), with classes of masses
  `13/40, 7/20, 13/40` and values

  ```
  ⎛ 0      1           49/50 ⎞
  ⎜ 1      557/14700   1     ⎟
  ⎝ 49/50  1           0     ⎠
  ```

Both are weighted step graphons (`Methods/Negative/WeightedStep.lean`).  The
masses and values are carried as natural numbers over common denominators: the
four-part graphon has masses `w/6000` and values `N/199800050`
(`199800050 = 2·99900025`, so `ε = 16092/199800050` and
`23/50 = 91908023/199800050`), the three-part graphon has masses `w/40` and
values `N/14700`.  Each row then evaluates its homomorphism density as one
`decide +kernel` sum of natural numbers.
-/

open Finset MeasureTheory

namespace Taeyoung.Methods.Negative

open Taeyoung

/-! ### The four-part graphon -/

/-- Class masses over `6000`: `δ = 3/6000 = 1/2000` and `(1-δ)/3 = 1999/6000`. -/
def extraVertexMass : Fin 4 → ℕ := ![3, 1999, 1999, 1999]

theorem extraVertexMass_sum : ∑ i, extraVertexMass i = 6000 := by decide

noncomputable instance : IsProbabilityMeasure (weightedMeasure 4 extraVertexMass 6000) :=
  isProbabilityMeasure_weightedMeasure 4 extraVertexMass 6000 extraVertexMass_sum (by norm_num)

/-- Cell values over `199800050`. -/
def extraVertexN : Fin 4 → Fin 4 → ℕ :=
  ![![0, 199800050, 91908023, 91908023],
    ![199800050, 16092, 199800050, 199800050],
    ![91908023, 199800050, 16092, 199800050],
    ![91908023, 199800050, 199800050, 16092]]

theorem extraVertexN_symm : ∀ i j, extraVertexN i j = extraVertexN j i := by decide
theorem extraVertexN_le : ∀ i j, extraVertexN i j ≤ 199800050 := by decide

/-- The four-part graphon of Section 5.2. -/
noncomputable def extraVertexW : Graphon (Fin 4) (weightedMeasure 4 extraVertexMass 6000) where
  toFun i j := (extraVertexN i j : ℝ) / (199800050 : ℝ)
  measurable := measurable_of_finite _
  nonneg i j := by positivity
  le_one i j := by
    rw [div_le_one (by norm_num : (0 : ℝ) < 199800050)]
    exact_mod_cast extraVertexN_le i j
  symm i j := by rw [extraVertexN_symm i j]

@[simp] lemma extraVertexW_apply (i j : Fin 4) :
    extraVertexW i j = (extraVertexN i j : ℝ) / (199800050 : ℝ) := rfl

theorem extraVertex_pairSum :
    ∑ z : Fin 2 → Fin 4, (∏ v, extraVertexMass (z v)) * extraVertexN (z 0) (z 1)
      = 4795201200000000 := by
  decide +kernel

/-- **The edge density is exactly `2/3`.** -/
theorem cliqueDensity_extraVertexW : cliqueDensity 2 extraVertexW = 2 / 3 := by
  rw [cliqueDensity, homDensity_weighted 4 extraVertexMass 6000 (⊤ : SimpleGraph (Fin 2))
    extraVertexMass_sum (by norm_num) extraVertexW (fun z ↦ extraVertexN (z 0) (z 1))
    (199800050 : ℝ) (fun z ↦ by rw [graphWeight_top_fin_two]; exact extraVertexW_apply _ _),
    extraVertex_pairSum]
  norm_num

/-! ### The three-part graphon -/

/-- Class masses over `40`: `13/40, 7/20, 13/40`. -/
def threePartMass : Fin 3 → ℕ := ![13, 14, 13]

theorem threePartMass_sum : ∑ i, threePartMass i = 40 := by decide

noncomputable instance : IsProbabilityMeasure (weightedMeasure 3 threePartMass 40) :=
  isProbabilityMeasure_weightedMeasure 3 threePartMass 40 threePartMass_sum (by norm_num)

/-- Cell values over `14700`. -/
def threePartN : Fin 3 → Fin 3 → ℕ :=
  ![![0, 14700, 14406], ![14700, 557, 14700], ![14406, 14700, 0]]

theorem threePartN_symm : ∀ i j, threePartN i j = threePartN j i := by decide
theorem threePartN_le : ∀ i j, threePartN i j ≤ 14700 := by decide

/-- The three-part graphon of Section 5.2. -/
noncomputable def threePartW : Graphon (Fin 3) (weightedMeasure 3 threePartMass 40) where
  toFun i j := (threePartN i j : ℝ) / (14700 : ℝ)
  measurable := measurable_of_finite _
  nonneg i j := by positivity
  le_one i j := by
    rw [div_le_one (by norm_num : (0 : ℝ) < 14700)]
    exact_mod_cast threePartN_le i j
  symm i j := by rw [threePartN_symm i j]

@[simp] lemma threePartW_apply (i j : Fin 3) :
    threePartW i j = (threePartN i j : ℝ) / (14700 : ℝ) := rfl

theorem threePart_pairSum :
    ∑ z : Fin 2 → Fin 3, (∏ v, threePartMass (z v)) * threePartN (z 0) (z 1) = 15680000 := by
  decide +kernel

/-- **The edge density is exactly `2/3`.** -/
theorem cliqueDensity_threePartW : cliqueDensity 2 threePartW = 2 / 3 := by
  rw [cliqueDensity, homDensity_weighted 3 threePartMass 40 (⊤ : SimpleGraph (Fin 2))
    threePartMass_sum (by norm_num) threePartW (fun z ↦ threePartN (z 0) (z 1))
    (14700 : ℝ) (fun z ↦ by rw [graphWeight_top_fin_two]; exact threePartW_apply _ _),
    threePart_pairSum]
  norm_num

end Taeyoung.Methods.Negative
