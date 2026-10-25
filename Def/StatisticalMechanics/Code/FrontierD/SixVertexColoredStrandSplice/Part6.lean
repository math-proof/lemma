/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkColoredStrandSlotEquivOfTrueCount
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (htrue : fkColoredTrueStrandSlotCount source =
      fkColoredTrueStrandSlotCount target) :
    FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T :=
  fkColoredStrandSlotEquivOfFiberCards source target
    (fkColoredStrandSlotFiberCards_of_trueCount_eq source target htrue)

end
end StatMech.FrontierD
