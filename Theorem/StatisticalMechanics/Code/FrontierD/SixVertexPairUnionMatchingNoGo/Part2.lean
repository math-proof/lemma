/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionMatchingNoGo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwo_not_completionUnionMatching :
    ¬ SixVertexHorizontalFineProfileCompletionUnionMatching
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero
      sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorTwo := by
  intro hmatching
  obtain ⟨matching, _, hpreserves⟩ :=
    hmatching sixVertexFourByTwoSourceFineProfile
  let source :=
    sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero
      sixVertexFourByTwoSectorTwo sixVertexFourByTwoSourceFineProfile
      sixVertexFourByTwoSourceFineProfilePair
  let target := matching source
  have hunion := hpreserves source
  have hsourceArrows :=
    sixVertexFineProfileCompletionPairArrows_equiv
      sixVertexFourByTwoSourceFineProfilePair
  change sixVertexHorizontalFineProfileCompletionPairArrows source =
      (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) at hsourceArrows
  unfold SixVertexHorizontalFineProfileCompletionPairUnionEqual at hunion
  rw [hsourceArrows] at hunion
  apply sixVertexFourByTwo_no_unionEqual_middlePair
    (sixVertexHorizontalFineProfileCompletionPairArrows target).1
    (sixVertexHorizontalFineProfileCompletionPairArrows target).2
  · exact target.2.1.1.2
  · exact target.2.2.1.2
  · exact target.2.1.2
  · exact hunion.1
  · exact hunion.2

end
end StatMech.FrontierD
