/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part9
open Finset


namespace StatMech.FrontierD

noncomputable section

def FKColoredStrandSplice.PreservesTotalC
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) : Prop :=
  fkColoredSlotPairEqualCount source splice.slotEquiv =
    fkColoredSlotPairEqualCount source (Equiv.refl _)

end
end StatMech.FrontierD
