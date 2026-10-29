import Taeyoung.Methods.Negative.StepGraphon

/-!
# Two step graphons on equal parts

`paper.pdf`, Section 5.2, uses two step graphons whose classes
all have the same mass:

* **Atlas 166, 172** — four equal parts `A₁, …, A₄`, with values
  ```
  ⎛ 0    1/4  1    1   ⎞
  ⎜ 1/4  0    1    1   ⎟
  ⎜ 1    1    0    1/4 ⎟
  ⎝ 1    1    1/4  0   ⎠
  ```
  of edge density `9/16` (`twoScaleW`): the two classes of `T₂`, each split in half,
  with value `1/4` between the halves.
* **Atlas 206** — three equal parts, with values
  ```
  ⎛ 1/4  1  1 ⎞
  ⎜ 1    0  1 ⎟
  ⎝ 1    1  0 ⎠
  ```
  of edge density `25/36` (`oneDiagW`): `T₃` with value `1/4` inside one class.

Both are rational step graphons on `Fin k` with the uniform measure, so
`Methods/Negative/StepGraphon.lean` applies with numerator matrix `N` and scale
`s = 4`.  The rows themselves (`Examples/Graph166.lean`, `Graph172.lean`,
`Graph206.lean`) evaluate the homomorphism densities.
-/

open Finset

namespace Taeyoung.Methods.Negative

open Taeyoung Taeyoung.Methods.PureChordal MeasureTheory

/-! ### The two witnesses -/

/-- The values of `twoScaleW`, as numerators over `s = 4`. -/
def twoScaleN : Fin 4 → Fin 4 → ℕ :=
  ![![0, 1, 4, 4], ![1, 0, 4, 4], ![4, 4, 0, 1], ![4, 4, 1, 0]]

theorem twoScaleN_symm : ∀ i j, twoScaleN i j = twoScaleN j i := by decide
theorem twoScaleN_le : ∀ i j, twoScaleN i j ≤ 4 := by decide

/-- The four-part graphon of Atlas 166 and 172, of edge density `9/16`. -/
noncomputable def twoScaleW : Graphon (Fin 4) (finiteUniformMeasure (Fin 4)) :=
  stepGraphon 4 4 twoScaleN twoScaleN_symm twoScaleN_le

/-- The values of `oneDiagW`, as numerators over `s = 4`. -/
def oneDiagN : Fin 3 → Fin 3 → ℕ :=
  ![![1, 4, 4], ![4, 0, 4], ![4, 4, 0]]

theorem oneDiagN_symm : ∀ i j, oneDiagN i j = oneDiagN j i := by decide
theorem oneDiagN_le : ∀ i j, oneDiagN i j ≤ 4 := by decide

/-- The three-part graphon of Atlas 206, of edge density `25/36`. -/
noncomputable def oneDiagW : Graphon (Fin 3) (finiteUniformMeasure (Fin 3)) :=
  stepGraphon 3 4 oneDiagN oneDiagN_symm oneDiagN_le

/-! ### Their edge densities -/

theorem sumPair_twoScale : ∑ z : Fin 2 → Fin 4, twoScaleN (z 0) (z 1) = 36 := by
  decide +kernel

theorem sumPair_oneDiag : ∑ z : Fin 2 → Fin 3, oneDiagN (z 0) (z 1) = 25 := by
  decide +kernel

theorem cliqueDensity_twoScale : cliqueDensity 2 twoScaleW = 9 / 16 := by
  rw [cliqueDensity_two_of_natWeight twoScaleW (fun z ↦ twoScaleN (z 0) (z 1))
    ((4 : ℝ)) (fun z ↦ rfl), sumPair_twoScale]
  norm_num

theorem cliqueDensity_oneDiag : cliqueDensity 2 oneDiagW = 25 / 36 := by
  rw [cliqueDensity_two_of_natWeight oneDiagW (fun z ↦ oneDiagN (z 0) (z 1))
    ((4 : ℝ)) (fun z ↦ rfl), sumPair_oneDiag]
  norm_num

end Taeyoung.Methods.Negative
