import Goodman.Methods.RootedSOS.Atlas43RawGroups

namespace Goodman.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem coefficient_cell_26_0 :
    (certificateCoefficient 26 0 ==
      targetCoefficient 26 0) = true := by
  decide +kernel

end Goodman.Methods.RootedSOS.Atlas43Coefficients
