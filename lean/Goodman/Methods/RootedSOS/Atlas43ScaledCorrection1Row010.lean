import Goodman.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Goodman.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem scaled_correction1_row_010 :
    ∀ j : Fin 48, stagedCorrectionRational₁Valid 10 j = true := by
  decide +kernel

end Goodman.Methods.RootedSOS.Atlas43Coefficients
