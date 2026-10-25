/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileDeficitSupport
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem actualDeficitTokenHall_iff_supportedMatching
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) :
    SixVertexHorizontalActualDeficitTokenHall T
        sourceLeft sourceRight targetLeft targetRight support ↔
      SixVertexHorizontalActualDeficitSupportedMatching T
        sourceLeft sourceRight targetLeft targetRight support := by
  constructor
  · intro hHall grade
    exact (Fintype.all_card_le_filter_rel_iff_exists_injective
      (support grade)).mp (hHall grade)
  · intro hmatching grade
    exact (Fintype.all_card_le_filter_rel_iff_exists_injective
      (support grade)).mpr (hmatching grade)

theorem configurationBigradeFibers_of_actualDeficitTokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop)
    (hHall : SixVertexHorizontalActualDeficitTokenHall T
      sourceLeft sourceRight targetLeft targetRight support) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  rw [configurationBigradeFibers_iff_horizontalChooseBigradeFibers,
    horizontalChooseBigradeFibers_iff_profileAggregate,
    profileAggregate_iff_signedNonnegative,
    profileSignedNonnegative_iff_actualDeficitEmbeddings]
  intro grade
  have hmatching :=
    (actualDeficitTokenHall_iff_supportedMatching T
      sourceLeft sourceRight targetLeft targetRight support).mp hHall grade
  rcases hmatching with ⟨matching, hinjective, hsupported⟩
  exact ⟨⟨matching, hinjective⟩⟩

end
end StatMech.FrontierD
