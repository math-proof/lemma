module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part4


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

def sixVertexFourByTwoCentralSourceEquiv :
    sixVertexFourByTwoCentralSourceIndex ≃
      (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorOne ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorThree) :=
  Equiv.prodCongr sixVertexFourByTwoSectorOneEquiv
    sixVertexFourByTwoSectorThreeEquiv

def sixVertexFourByTwoCentralTargetEquiv :
    (Fin 50 × Fin 50) ≃
      (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorTwo ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorTwo) :=
  Equiv.prodCongr sixVertexFourByTwoSectorTwoEquiv
    sixVertexFourByTwoSectorTwoEquiv

end
end StatMech.FrontierD
