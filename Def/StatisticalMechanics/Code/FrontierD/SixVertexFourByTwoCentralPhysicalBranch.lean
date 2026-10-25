/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoSectorThree :
    Fin (sixVertexFourByTwoTorus.width + 1) :=
  ⟨3, by norm_num [sixVertexFourByTwoTorus]⟩

def sixVertexFourByTwoSectorThreeConfiguration (i : Fin 28) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorThree :=
  ⟨sixVertexArrowsComplement (sixVertexFourByTwoSectorOneConfiguration i).1,
    sixVertexArrowsComplement_iceRule
      (sixVertexFourByTwoSectorOneConfiguration i).2.1, by
      change sixVertexUpCount (fun x =>
        !(sixVertexFourByTwoSectorOneConfiguration i).1.vertical
          (x, svFinLast sixVertexFourByTwoTorus.height_pos)) = 3
      rw [sixVertexUpCount_complement]
      have hsector := (sixVertexFourByTwoSectorOneConfiguration i).2.2
      change sixVertexUpCount (fun x =>
        (sixVertexFourByTwoSectorOneConfiguration i).1.vertical
          (x, svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 at hsector
      rw [hsector]
      norm_num [sixVertexFourByTwoTorus]⟩

end
end StatMech.FrontierD
