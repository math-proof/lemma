/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation


namespace StatMech.FrontierD

noncomputable section

structure FKColoredResolvedUnitCross
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) where
  mask : T.Vertex -> Bool
  bondCoherent : FKColoredVertexCrossBondCoherent source mask
  seamDelta_false : fkColoredVertexCrossSeamDelta source mask
    bondCoherent false = 1
  seamDelta_true : fkColoredVertexCrossSeamDelta source mask
    bondCoherent true = -1
  twoCycle : sixVertexPairAtMostTwoCycleRelated
    ((source false).arrows, (source true).arrows)
    ((fkColoredVertexCrossTarget source mask bondCoherent false).arrows,
      (fkColoredVertexCrossTarget source mask bondCoherent true).arrows)

end
end StatMech.FrontierD
