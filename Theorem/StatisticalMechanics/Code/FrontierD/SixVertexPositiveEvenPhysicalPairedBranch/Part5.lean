module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part9
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part4
open Filter Matrix Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFour_twoRowCommonFactor_cardinality_obstruction :
    ¬ ∃ factor : Nat,
      (4 * 50) * factor = 16 * 1682 ∧
        (28 * 28) * factor = 628 * 628 := by
  rintro ⟨factor, hsource, _htarget⟩
  norm_num at hsource
  omega


end
end StatMech.FrontierD
