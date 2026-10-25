/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoSectorThreeEquiv :
    Fin 28 ≃ SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorThree :=
  Equiv.ofBijective sixVertexFourByTwoSectorThreeConfiguration
    ⟨sixVertexFourByTwoSectorThreeConfiguration_injective,
      sixVertexFourByTwoSectorThreeConfiguration_surjective⟩

end
end StatMech.FrontierD
