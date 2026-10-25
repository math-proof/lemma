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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part2
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoPhysicalSourceEmbedding :
    SixVertexConfigurationPhysicalSource
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne_pos
      sixVertexFourByTwoSectorOne_lt_width ↪
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) where
  toFun source :=
    (⟨source.1.1, source.1.2.1, by
        simpa [sixVertexFourByTwoSectorZero,
          sixVertexFourByTwoSectorOne] using source.1.2.2⟩,
      ⟨source.2.1, source.2.2.1, by
        simpa [sixVertexFourByTwoSectorTwo,
          sixVertexFourByTwoSectorOne] using source.2.2.2⟩)
  inj' := by
    intro first second heq
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun pair => pair.1.1) heq
    · apply Subtype.ext
      exact congrArg (fun pair => pair.2.1) heq

end
end StatMech.FrontierD
