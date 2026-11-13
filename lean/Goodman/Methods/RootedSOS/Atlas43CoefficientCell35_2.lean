import Goodman.Methods.RootedSOS.Atlas43RawGroups

namespace Goodman.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem coefficient_cell_35_2 :
    (certificateCoefficient 35 2 ==
      targetCoefficient 35 2) = true := by
  decide +kernel

end Goodman.Methods.RootedSOS.Atlas43Coefficients
