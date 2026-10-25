/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def FKColoredStrandSpliceBondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T) : Prop :=
  forall x : FKLayeredMedialDart T,
    fkColoredStrandSpliceRawColor source targetPairing slotEquiv
        (fkLayeredBondMate T x) =
      fkColoredStrandSpliceRawColor source targetPairing slotEquiv x


end
end StatMech.FrontierD
