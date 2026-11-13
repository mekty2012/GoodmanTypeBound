import Goodman.Methods.RootedSOS.Atlas43Flags
import Goodman.Methods.RootedSOS.FixedDensity

namespace Goodman.Methods.RootedSOS.Atlas43FixedDensity

open Goodman.Methods.RootedSOS
open Goodman.Methods.RootedSOS.Atlas43Flags

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem decompositions_rows_24 : ∀ (a : Fin 8) (b : Fin 64),
    decompositionValid (gluedOrdinaryGraph
      ⟨24 + a.1, by omega⟩ b) = true := by
  decide +kernel

end Goodman.Methods.RootedSOS.Atlas43FixedDensity
