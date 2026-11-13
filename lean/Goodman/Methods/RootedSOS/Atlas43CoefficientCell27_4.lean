import Goodman.Methods.RootedSOS.Atlas43RawGroups

namespace Goodman.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem coefficient_cell_27_4 :
    (certificateCoefficient 27 4 ==
      targetCoefficient 27 4) = true := by
  decide +kernel

end Goodman.Methods.RootedSOS.Atlas43Coefficients
