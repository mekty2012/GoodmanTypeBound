import Goodman.Methods.RootedSOS.Atlas43RawGroups

namespace Goodman.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem coefficient_cell_00_4 :
    (certificateCoefficient 0 4 ==
      targetCoefficient 0 4) = true := by
  decide +kernel

end Goodman.Methods.RootedSOS.Atlas43Coefficients
