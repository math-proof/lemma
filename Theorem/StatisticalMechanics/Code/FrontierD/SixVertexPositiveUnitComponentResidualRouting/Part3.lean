/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part4


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentResidualOrbitCover

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


theorem matching_physical
    (cover : SixVertexPositiveUnitComponentResidualOrbitCover T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexPositiveUnitComponentResidualSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
        T middle hmiddle_pos hmiddle_lt grade (cover.matching source) =
      cover.physical.matching source := by
  let covered := cover.physical.sourceCover source
  change sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
      T middle hmiddle_pos hmiddle_lt grade
        (cover.targetLift
          ⟨covered.1,
            cover.physical.toAtlas.localMatching covered.1 covered.2⟩) =
    cover.physical.targetEmbedding
      ⟨covered.1,
        cover.physical.toAtlas.localMatching covered.1 covered.2⟩
  exact cover.targetLift_physical _ _


theorem matching_supported
    (cover : SixVertexPositiveUnitComponentResidualOrbitCover T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexPositiveUnitComponentResidualSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (cover.matching source) := by
  change sixVertexPairAtMostTwoCycleFineRelated
    ((sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.1,
      (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.1)
    ((sixVertexHorizontalActualSurplusConfigurationPair
        (cover.matching source)).1.1.1,
      (sixVertexHorizontalActualSurplusConfigurationPair
        (cover.matching source)).1.2.1)
  have hrelated := cover.physical.matching_fineRelated source
  rw [cover.sourcePhysical source] at hrelated
  rw [← cover.matching_physical source] at hrelated
  exact hrelated

end SixVertexPositiveUnitComponentResidualOrbitCover
end
end StatMech.FrontierD
