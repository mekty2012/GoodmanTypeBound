import Goodman.Methods.RootedSOS.S4ClassificationFastGroupBase

namespace Goodman.Methods.RootedSOS.S4Classification

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem fast_group_row_008 : ∀ left right : Fin 16,
    fastGroupValid 8 left right = true := by
  decide +kernel

end Goodman.Methods.RootedSOS.S4Classification
