/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part6


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoCentralConfigurationMatchingEmbedding :
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorThree) ↪
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) where
  toFun := sixVertexFourByTwoCentralConfigurationMatching
  inj' := sixVertexFourByTwoCentralConfigurationMatching_injective

def sixVertexFourByTwoCentralPhysicalBranch (choice : Bool) :=
  if choice then
    sixVertexFourByTwoCentralConfigurationMatchingEmbedding.trans
      (Equiv.prodComm _ _).toEmbedding
  else sixVertexFourByTwoCentralConfigurationMatchingEmbedding

end
end StatMech.FrontierD
