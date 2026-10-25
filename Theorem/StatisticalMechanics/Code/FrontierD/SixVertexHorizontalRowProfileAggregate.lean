/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileSupport.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexHorizontalActualDeficitRowProfileFiber
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (rowProfile : SixVertexHorizontalRowZeroProfile T) :
    Fintype.card
        {source : SixVertexHorizontalActualDeficitTokens T grade
            sourceLeft sourceRight targetLeft targetRight //
          sixVertexHorizontalActualDeficitRowProfile source = rowProfile} =
      ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
        sixVertexHorizontalProfileDeficit
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1) := by
  rw [Fintype.card_congr
    (sixVertexHorizontalActualDeficitRowProfileEquiv T grade
      sourceLeft sourceRight targetLeft targetRight rowProfile),
    Fintype.card_sigma]
  simp

theorem card_sixVertexHorizontalActualSurplusRowProfileFiber
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (rowProfile : SixVertexHorizontalRowZeroProfile T) :
    Fintype.card
        {target : SixVertexHorizontalActualSurplusTokens T grade
            sourceLeft sourceRight targetLeft targetRight //
          sixVertexHorizontalActualSurplusRowProfile target = rowProfile} =
      ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
        sixVertexHorizontalProfileSurplus
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1) := by
  rw [Fintype.card_congr
    (sixVertexHorizontalActualSurplusRowProfileEquiv T grade
      sourceLeft sourceRight targetLeft targetRight rowProfile),
    Fintype.card_sigma]
  simp

end
end StatMech.FrontierD
