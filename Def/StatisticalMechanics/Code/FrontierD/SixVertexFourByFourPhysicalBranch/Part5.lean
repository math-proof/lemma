/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCount
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourPhysicalBranch.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexFourByFourMiddleOneRowCyclePairedBranchEmbeddings :
    SixVertexPhysicalRowCyclePairedBranchEmbeddings sixVertexFourByFourTorus
      sixVertexFourByFourSectorOne
      sixVertexFourByFourSectorOne_pos
      sixVertexFourByFourSectorOne_lt_width :=
  sixVertexPhysicalRowCyclePairedBranchEmbeddings_of_exactGradeCapacity
    sixVertexFourByFourMiddleOneExactGradeCapacity

noncomputable def sixVertexFourByFourMiddleTwoRowCyclePairedBranchEmbeddings :
    SixVertexPhysicalRowCyclePairedBranchEmbeddings sixVertexFourByFourTorus
      sixVertexFourByFourSectorTwo
      sixVertexFourByFourSectorTwo_pos
      sixVertexFourByFourSectorTwo_lt_width :=
  sixVertexPhysicalRowCyclePairedBranchEmbeddings_of_exactGradeCapacity
    sixVertexFourByFourMiddleTwoExactGradeCapacity

noncomputable def sixVertexFourByFourMiddleOnePhysicalPairedBranchEmbeddings :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      sixVertexFourByFourTorus sixVertexFourByFourSectorOne
      sixVertexFourByFourSectorOne_pos
      sixVertexFourByFourSectorOne_lt_width :=
  sixVertexFourByFourMiddleOneRowCyclePairedBranchEmbeddings.toPhysical

noncomputable def sixVertexFourByFourMiddleTwoPhysicalPairedBranchEmbeddings :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      sixVertexFourByFourTorus sixVertexFourByFourSectorTwo
      sixVertexFourByFourSectorTwo_pos
      sixVertexFourByFourSectorTwo_lt_width :=
  sixVertexFourByFourMiddleTwoRowCyclePairedBranchEmbeddings.toPhysical

noncomputable def sixVertexFourByFourMiddleThreePhysicalPairedBranchEmbeddings :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      sixVertexFourByFourTorus sixVertexFourByFourSectorThree
      (by norm_num [sixVertexFourByFourSectorThree])
      (by norm_num [sixVertexFourByFourSectorThree,
        sixVertexFourByFourTorus]) := by
  simpa [sixVertexFourByFourSectorOne, sixVertexFourByFourSectorThree,
    sixVertexFourByFourTorus, sixVertexPhysicalParticleHoleMiddle] using
    sixVertexFourByFourMiddleOnePhysicalPairedBranchEmbeddings.particleHole

end
end StatMech.FrontierD
