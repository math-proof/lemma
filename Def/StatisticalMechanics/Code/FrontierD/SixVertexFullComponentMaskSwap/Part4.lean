/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexFullDisagreementColoredTarget
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    FKColoredLoopPairingPair T :=
  fkColoredFullSwapTarget source
    (sixVertexFullDisagreementVertexMask mask)
    (hmask.fullSwapBondCoherent source mask)

end
end StatMech.FrontierD
