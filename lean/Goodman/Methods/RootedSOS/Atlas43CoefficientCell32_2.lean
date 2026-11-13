import Goodman.Methods.RootedSOS.Atlas43RawGroups

namespace Goodman.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem coefficient_cell_32_2 :
    (certificateCoefficient 32 2 ==
      targetCoefficient 32 2) = true := by
  decide +kernel

end Goodman.Methods.RootedSOS.Atlas43Coefficients
