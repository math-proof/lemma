module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part6
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

def SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches : Prop :=
  forall r k : Nat,
    SixVertexPositiveEvenTracePhysicalPairedBranches
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))


end
end StatMech.FrontierD
