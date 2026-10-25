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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part3
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwo_sectorTrace_logConcave_of_physicalBranches
    {c : Real} (hc : 1 <= c) :
    Matrix.trace (sixVertexSectorTransfer 4 0 c ^ 2) *
        Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 2) <=
      Matrix.trace (sixVertexSectorTransfer 4 1 c ^ 2) ^ 2 := by
  simpa [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne] using
    sixVertexSectorTrace_logConcave_of_physicalPairedBranches
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne_pos
      sixVertexFourByTwoSectorOne_lt_width
      hc sixVertexFourByTwoPhysicalPairedBranchEmbeddings


theorem sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches :
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num))
        ⟨1, by norm_num [sixVertexPositiveEvenTorus]⟩
        (by norm_num) (by norm_num [sixVertexPositiveEvenTorus])) := by
  simpa [sixVertexPositiveEvenTorus, sixVertexPositiveEvenHeight,
    sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne] using
    (show Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        (by norm_num [sixVertexFourByTwoSectorOne])
        (by norm_num [sixVertexFourByTwoSectorOne,
          sixVertexFourByTwoTorus])) from
      ⟨sixVertexFourByTwoPhysicalPairedBranchEmbeddings⟩)


theorem sixVertexFourByTwo_positiveEvenBaseCentralPhysicalPairedBranches :
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num))
        ⟨2, by norm_num [sixVertexPositiveEvenTorus]⟩
        (by norm_num) (by norm_num [sixVertexPositiveEvenTorus])) := by
  simpa [sixVertexPositiveEvenTorus, sixVertexPositiveEvenHeight,
    sixVertexFourByTwoTorus, sixVertexFourByTwoSectorTwo] using
    (show Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo
        sixVertexFourByTwoSectorTwo_pos
        sixVertexFourByTwoSectorTwo_lt_width) from
      ⟨sixVertexFourByTwoCentralPhysicalPairedBranchEmbeddings⟩)


theorem sixVertexFourByTwo_positiveEvenBaseParticleHolePhysicalPairedBranches :
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num))
        ⟨3, by norm_num [sixVertexPositiveEvenTorus]⟩
        (by norm_num) (by norm_num [sixVertexPositiveEvenTorus])) := by
  simpa [sixVertexPositiveEvenTorus, sixVertexPositiveEvenHeight,
    sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne,
    sixVertexPhysicalParticleHoleMiddle] using
    (show Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        sixVertexFourByTwoTorus
        (sixVertexPhysicalParticleHoleMiddle sixVertexFourByTwoSectorOne)
        (sixVertexPhysicalParticleHoleMiddle_pos sixVertexFourByTwoSectorOne
          sixVertexFourByTwoSectorOne_lt_width)
        (sixVertexPhysicalParticleHoleMiddle_lt sixVertexFourByTwoSectorOne
          sixVertexFourByTwoSectorOne_pos)) from
      ⟨sixVertexFourByTwoPhysicalPairedBranchEmbeddings.particleHole⟩)


theorem sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches_allSectors
    (n : Nat) (hn0 : 0 < n) (hn4 : n < 4) :
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num))
        ⟨n, by norm_num [sixVertexPositiveEvenTorus]; omega⟩ hn0 hn4) := by
  have hn : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn with rfl | rfl | rfl
  · simpa using sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches
  · simpa using sixVertexFourByTwo_positiveEvenBaseCentralPhysicalPairedBranches
  · simpa using
      sixVertexFourByTwo_positiveEvenBaseParticleHolePhysicalPairedBranches


end
end StatMech.FrontierD
