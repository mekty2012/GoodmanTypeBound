import Goodman.Methods.RootedSOS.Atlas43CoefficientBase

namespace Goodman.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem block0_witness_row_102 :
    block₀WitnessRowValid 102 = true := by
  decide +kernel

end Goodman.Methods.RootedSOS.Atlas43Coefficients
