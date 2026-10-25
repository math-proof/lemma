/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkColoredStrandSlotEquivOfFiberCards
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (hcard : forall color : Bool,
      Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor target slot = color} =
        Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor source slot = color}) :
    FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T :=
  Equiv.ofFiberEquiv fun color =>
    Fintype.equivOfCardEq (hcard color)

end
end StatMech.FrontierD
