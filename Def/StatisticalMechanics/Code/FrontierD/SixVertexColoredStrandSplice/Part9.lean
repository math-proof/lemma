/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkColoredSlotPairEqualCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T) : Nat :=
  ∑ v : T.Vertex, (
    (if fkColoredLayeredSlotColor source (slotEquiv (false, v, false)) =
        fkColoredLayeredSlotColor source (slotEquiv (false, v, true))
      then 1 else 0) +
    (if fkColoredLayeredSlotColor source (slotEquiv (true, v, false)) =
        fkColoredLayeredSlotColor source (slotEquiv (true, v, true))
      then 1 else 0))

end
end StatMech.FrontierD
