module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexSwapPhysicalTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexConfigurationPhysicalTarget T middle) :
    SixVertexConfigurationPhysicalTarget T middle :=
  (target.2, target.1)

end
end StatMech.FrontierD
