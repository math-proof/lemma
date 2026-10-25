/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation


namespace StatMech.FrontierD

noncomputable section

def FKColoredResolvedUnitCross.target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    FKColoredLoopPairingPair T :=
  fkColoredVertexCrossTarget source cross.mask cross.bondCoherent

end
end StatMech.FrontierD
