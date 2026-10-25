/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoPhysicalBranch_distinct
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    sixVertexFourByTwoPhysicalBranch false source ≠
      sixVertexFourByTwoPhysicalBranch true source := by
  intro heq
  have hcomponents := congrArg Prod.fst heq
  exact sixVertexFourByTwoConfigurationPairMatching_components_ne source
    (by simpa [sixVertexFourByTwoPhysicalBranch] using hcomponents)

theorem sixVertexFourByTwoPhysicalBranch_totalC
    (choice : Bool)
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoPhysicalBranch choice source) =
      sixVertexConfigurationPairTotalCPhysical source := by
  have hrelated :=
    sixVertexFourByTwoConfigurationPairMatching_fineRelated source
  have htotal := sixVertexPairAtMostTwoCycleFineRelated_totalC hrelated
  cases choice <;>
    simpa [sixVertexFourByTwoPhysicalBranch,
      sixVertexConfigurationPairTotalCPhysical, Nat.add_comm] using htotal.symm

theorem sixVertexFourByTwoSectorOne_pos :
    0 < sixVertexFourByTwoSectorOne.val := by
  norm_num [sixVertexFourByTwoSectorOne]

theorem sixVertexFourByTwoSectorOne_lt_width :
    sixVertexFourByTwoSectorOne.val < sixVertexFourByTwoTorus.width := by
  norm_num [sixVertexFourByTwoSectorOne, sixVertexFourByTwoTorus]


end
end StatMech.FrontierD
