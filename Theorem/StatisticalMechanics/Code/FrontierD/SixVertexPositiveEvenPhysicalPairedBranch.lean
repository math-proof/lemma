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
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoMatchingTable_components_ne (i : Fin 200) :
    (sixVertexFourByTwoMatchingTable i).1 ≠
      (sixVertexFourByTwoMatchingTable i).2 := by
  fin_cases i <;> decide

theorem sixVertexFourByTwoMatchingIndex_components_ne (i : Fin 4 × Fin 50) :
    (sixVertexFourByTwoMatchingIndex i).1 ≠
      (sixVertexFourByTwoMatchingIndex i).2 := by
  exact sixVertexFourByTwoMatchingTable_components_ne
    (finProdFinEquiv (m := 4) (n := 50) i)


theorem sixVertexFourByTwoConfigurationPairMatching_components_ne
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    (sixVertexFourByTwoConfigurationPairMatching source).1 ≠
      (sixVertexFourByTwoConfigurationPairMatching source).2 := by
  let i := sixVertexFourByTwoSourcePairEquiv.symm source
  have hindex := sixVertexFourByTwoMatchingIndex_components_ne i
  intro heq
  apply hindex
  apply sixVertexFourByTwoSectorOneEquiv.injective
  simpa [sixVertexFourByTwoConfigurationPairMatching,
    sixVertexFourByTwoTargetPairEquiv, i] using heq

end
end StatMech.FrontierD
