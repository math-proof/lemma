module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoCentralConfigurationMatching
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorThree) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo :=
  sixVertexFourByTwoCentralTargetEquiv
    (sixVertexFourByTwoCentralIndexMatching
      (sixVertexFourByTwoCentralSourceEquiv.symm source)).1

end
end StatMech.FrontierD
