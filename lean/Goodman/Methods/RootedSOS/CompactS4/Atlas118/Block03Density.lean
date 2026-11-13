import Goodman.Methods.RootedSOS.CompactS4.Atlas118.Block03PSD
import Goodman.Methods.RootedSOS.CompactS4.Atlas118.Block03Expansion
import Goodman.Methods.RootedSOS.CompactS4.Young211
import Goodman.Methods.RootedSOS.MatrixFlagDensity

namespace Goodman.Methods.RootedSOS.CompactS4.Atlas118.Block03
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def density (W : Goodman.Graphon Ω μ) (s : Real) : Real :=
  ∑ i : Fin 30, ∑ j : Fin 30, ((H i j : Real) + ((H i (30+j) : Real)+(H (30+i) j : Real))*s + (H (30+i) (30+j) : Real)*s^2) *
    (∑ g : Fin 143, (Young211.pulled g i j : Real) *
      (Goodman.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Goodman.homDensity (S4Classification.coreGraph6 g) W))

theorem density_nonneg (W : Goodman.Graphon Ω μ) (s : Real) : 0 ≤ density W s := by
  have h := integer_flag_density_nonneg (order := 2) (n := 59)
    S4Flags.flagLabelGraph S4Flags.flagBranchNeighbors
    (fun a i => (Young211.TInt a i : Real))
    (fun ui k => N (finProdFinEquiv ui) k) (fun i j => G i j)
    (fun ui vj => H (finProdFinEquiv ui) (finProdFinEquiv vj))
    gram_nonneg (fun a b => expanded_entries_exact (finProdFinEquiv a) (finProdFinEquiv b)) W s
  change 0 ≤ ∑ ui : Fin 2 × Fin 30, ∑ vj : Fin 2 × Fin 30,
    (H (finProdFinEquiv ui) (finProdFinEquiv vj) : Real) * s^(ui.1.1+vj.1.1) *
      (∑ a : Fin 352, ∑ b : Fin 352,
        (Young211.TInt a ui.2 : Real)*(Young211.TInt b vj.2 : Real)*
          Goodman.homDensity (S4Flags.gluedGraph a b) W) at h
  simp_rw [Young211.pair_basis_density] at h
  rw [two_layer_sum H
    (fun i j : Fin 30 => ∑ g : Fin 143, (Young211.pulled g i j : Real) *
      (Goodman.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Goodman.homDensity (S4Classification.coreGraph6 g) W)) s] at h
  exact h

#print axioms density_nonneg
end Goodman.Methods.RootedSOS.CompactS4.Atlas118.Block03
