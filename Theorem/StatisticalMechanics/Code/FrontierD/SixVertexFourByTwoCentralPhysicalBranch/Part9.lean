/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part10


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoCentral_sectorTrace_logConcave_of_physicalBranches
    {c : Real} (hc : 1 ≤ c) :
    Matrix.trace (sixVertexSectorTransfer 4 1 c ^ 2) *
        Matrix.trace (sixVertexSectorTransfer 4 3 c ^ 2) ≤
      Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 2) ^ 2 := by
  simpa [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorTwo] using
    sixVertexSectorTrace_logConcave_of_physicalPairedBranches
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoSectorTwo_pos
      sixVertexFourByTwoSectorTwo_lt_width hc
      sixVertexFourByTwoCentralPhysicalPairedBranchEmbeddings

end
end StatMech.FrontierD
