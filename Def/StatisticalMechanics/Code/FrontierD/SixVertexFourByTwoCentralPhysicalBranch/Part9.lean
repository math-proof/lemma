/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part7


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoCentralPhysicalSourceEmbedding :
    SixVertexConfigurationPhysicalSource sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorTwo_pos
      sixVertexFourByTwoSectorTwo_lt_width ↪
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorThree) where
  toFun source :=
    (⟨source.1.1, source.1.2.1, by
        simpa [sixVertexFourByTwoSectorOne,
          sixVertexFourByTwoSectorTwo] using source.1.2.2⟩,
      ⟨source.2.1, source.2.2.1, by
        simpa [sixVertexFourByTwoSectorThree,
          sixVertexFourByTwoSectorTwo] using source.2.2.2⟩)
  inj' := by
    intro first second heq
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun pair => pair.1.1) heq
    · apply Subtype.ext
      exact congrArg (fun pair => pair.2.1) heq

end
end StatMech.FrontierD
