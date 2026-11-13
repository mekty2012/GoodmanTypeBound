import Goodman.Methods.RootedSOS.Atlas43RawGroupCellBase

namespace Goodman.Methods.RootedSOS.Atlas43Coefficients

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem exceptional_pair_weight1_10 :
    exceptionalPairWeight₁EncodingValid 10 = true := by
  decide +kernel

end Goodman.Methods.RootedSOS.Atlas43Coefficients
