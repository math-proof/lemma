/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileHall
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexHorizontalProfileTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (left right : Fin (T.width + 1)) :
    Fintype.card (SixVertexHorizontalProfileTokens T grade left right) =
      ∑ profile : SixVertexHorizontalPairCompletionProfile T,
        sixVertexHorizontalPairProfileMultiplicity T grade profile *
          sixVertexHorizontalPairProfileChooseWeight left right profile := by
  rw [Fintype.card_sigma]
  simp


theorem profileAggregate_iff_tokenEmbeddings
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalProfileAggregateDominates T
        sourceLeft sourceRight targetLeft targetRight ↔
      forall grade, Nonempty
        (SixVertexHorizontalProfileTokens T grade sourceLeft sourceRight ↪
          SixVertexHorizontalProfileTokens T grade targetLeft targetRight) := by
  unfold SixVertexHorizontalProfileAggregateDominates
  constructor
  · intro hdom grade
    apply Function.Embedding.nonempty_of_card_le
    rw [card_sixVertexHorizontalProfileTokens,
      card_sixVertexHorizontalProfileTokens]
    exact hdom grade
  · intro hemb grade
    rw [<- card_sixVertexHorizontalProfileTokens,
      <- card_sixVertexHorizontalProfileTokens]
    exact Function.Embedding.nonempty_iff_card_le.mp (hemb grade)


end
end StatMech.FrontierD
