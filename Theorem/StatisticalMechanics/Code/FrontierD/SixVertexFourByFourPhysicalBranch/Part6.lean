/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCount
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourPhysicalBranch.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourPhysicalPairedBranchEmbeddings_allSectors
    (n : Nat) (hn0 : 0 < n) (hn4 : n < 4) :
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        sixVertexFourByFourTorus
        ⟨n, by norm_num [sixVertexFourByFourTorus]; omega⟩ hn0 hn4) := by
  have hn : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn with rfl | rfl | rfl
  · simpa [sixVertexFourByFourSectorOne] using
      (show Nonempty
        (SixVertexConfigurationPhysicalPairedBranchEmbeddings
          sixVertexFourByFourTorus sixVertexFourByFourSectorOne
          sixVertexFourByFourSectorOne_pos
          sixVertexFourByFourSectorOne_lt_width) from
        ⟨sixVertexFourByFourMiddleOnePhysicalPairedBranchEmbeddings⟩)
  · simpa [sixVertexFourByFourSectorTwo] using
      (show Nonempty
        (SixVertexConfigurationPhysicalPairedBranchEmbeddings
          sixVertexFourByFourTorus sixVertexFourByFourSectorTwo
          sixVertexFourByFourSectorTwo_pos
          sixVertexFourByFourSectorTwo_lt_width) from
        ⟨sixVertexFourByFourMiddleTwoPhysicalPairedBranchEmbeddings⟩)
  · simpa [sixVertexFourByFourSectorThree] using
      (show Nonempty
        (SixVertexConfigurationPhysicalPairedBranchEmbeddings
          sixVertexFourByFourTorus sixVertexFourByFourSectorThree
          (by norm_num [sixVertexFourByFourSectorThree])
          (by norm_num [sixVertexFourByFourSectorThree,
            sixVertexFourByFourTorus])) from
        ⟨sixVertexFourByFourMiddleThreePhysicalPairedBranchEmbeddings⟩)

end
end StatMech.FrontierD
