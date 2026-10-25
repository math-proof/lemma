/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation


namespace StatMech.FrontierD

noncomputable section

theorem FKColoredResolvedUnitCross.target_bigrade
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    (fkColoredLoopPairingPairTotalC cross.target,
        fkColoredTrueStrandSlotCount cross.target) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) :=
  fkColoredVertexCrossTarget_bigrade source cross.mask cross.bondCoherent

theorem FKColoredResolvedUnitCross.target_fine
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((cross.target false).arrows.horizontal,
          (cross.target true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal) :=
  fkColoredVertexCrossTarget_boundedFineRowProfile source cross.mask
    cross.bondCoherent

theorem FKColoredResolvedUnitCross.target_twoCycleFine
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((source false).arrows, (source true).arrows)
      ((cross.target false).arrows, (cross.target true).arrows) :=
  ⟨cross.twoCycle, cross.target_fine.symm⟩


end
end StatMech.FrontierD
