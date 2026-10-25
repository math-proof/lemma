/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileDeficitSupport
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexHorizontalActualDeficitPair_bigrade
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    sixVertexHorizontalPairBigrade
        (sixVertexHorizontalActualDeficitPair token) = grade :=
  token.2.1.1.2

@[simp] theorem sixVertexHorizontalActualSurplusPair_bigrade
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    sixVertexHorizontalPairBigrade
        (sixVertexHorizontalActualSurplusPair token) = grade :=
  token.2.1.1.2

theorem card_sixVertexHorizontalActualDeficitTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Fintype.card (SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) =
      Fintype.card (SixVertexHorizontalProfileDeficitTokens T grade
        sourceLeft sourceRight targetLeft targetRight) := by
  rw [Fintype.card_sigma, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro profile hprofile
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    card_sixVertexHorizontalPairProfileFiber]

theorem card_sixVertexHorizontalActualSurplusTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Fintype.card (SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) =
      Fintype.card (SixVertexHorizontalProfileSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight) := by
  rw [Fintype.card_sigma, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro profile hprofile
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    card_sixVertexHorizontalPairProfileFiber]

theorem profileSignedNonnegative_iff_actualDeficitEmbeddings
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalProfileAggregateSignedNonnegative T
        sourceLeft sourceRight targetLeft targetRight ↔
      forall grade, Nonempty
        (SixVertexHorizontalActualDeficitTokens T grade
            sourceLeft sourceRight targetLeft targetRight ↪
          SixVertexHorizontalActualSurplusTokens T grade
            sourceLeft sourceRight targetLeft targetRight) := by
  rw [profileSignedNonnegative_iff_deficit_le_surplus]
  constructor
  · intro hcard grade
    apply Function.Embedding.nonempty_of_card_le
    rw [card_sixVertexHorizontalActualDeficitTokens,
      card_sixVertexHorizontalActualSurplusTokens]
    exact hcard grade
  · intro hemb grade
    rw [← card_sixVertexHorizontalActualDeficitTokens,
      ← card_sixVertexHorizontalActualSurplusTokens]
    exact Function.Embedding.nonempty_iff_card_le.mp (hemb grade)

end
end StatMech.FrontierD
