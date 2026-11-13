import Goodman.Methods.RootedSOS.CompactS4.Atlas169.Block09PSD
import Goodman.Methods.RootedSOS.CompactS4.Atlas169.Block09Expansion
import Goodman.Methods.RootedSOS.CompactS4.Young1111
import Goodman.Methods.RootedSOS.MatrixFlagDensity

namespace Goodman.Methods.RootedSOS.CompactS4.Atlas169.Block09
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def density (W : Goodman.Graphon Ω μ) (s : Real) : Real :=
  ∑ i : Fin 6, ∑ j : Fin 6, ((H i j : Real)) *
    (∑ g : Fin 143, (Young1111.pulled g i j : Real) *
      (Goodman.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Goodman.homDensity (S4Classification.coreGraph6 g) W))

theorem density_nonneg (W : Goodman.Graphon Ω μ) (s : Real) : 0 ≤ density W s := by
  have h := integer_flag_density_nonneg (order := 1) (n := 6)
    S4Flags.flagLabelGraph S4Flags.flagBranchNeighbors
    (fun a i => (Young1111.TInt a i : Real))
    (fun ui k => N (finProdFinEquiv ui) k) (fun i j => G i j)
    (fun ui vj => H (finProdFinEquiv ui) (finProdFinEquiv vj))
    gram_nonneg (fun a b => expanded_entries_exact (finProdFinEquiv a) (finProdFinEquiv b)) W s
  change 0 ≤ ∑ ui : Fin 1 × Fin 6, ∑ vj : Fin 1 × Fin 6,
    (H (finProdFinEquiv ui) (finProdFinEquiv vj) : Real) * s^(ui.1.1+vj.1.1) *
      (∑ a : Fin 352, ∑ b : Fin 352,
        (Young1111.TInt a ui.2 : Real)*(Young1111.TInt b vj.2 : Real)*
          Goodman.homDensity (S4Flags.gluedGraph a b) W) at h
  simp_rw [Young1111.pair_basis_density] at h
  rw [one_layer_sum H
    (fun i j : Fin 6 => ∑ g : Fin 143, (Young1111.pulled g i j : Real) *
      (Goodman.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Goodman.homDensity (S4Classification.coreGraph6 g) W)) s] at h
  exact h

#print axioms density_nonneg
end Goodman.Methods.RootedSOS.CompactS4.Atlas169.Block09
