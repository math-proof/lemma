/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileHall
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem profileAggregate_of_tokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileTokens T grade sourceLeft sourceRight ->
        SixVertexHorizontalProfileTokens T grade targetLeft targetRight -> Prop)
    (hHall : SixVertexHorizontalProfileTokenHall T
      sourceLeft sourceRight targetLeft targetRight support) :
    SixVertexHorizontalProfileAggregateDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  rw [profileAggregate_iff_tokenEmbeddings]
  intro grade
  have hmatching :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (support grade)).mp (hHall grade)
  rcases hmatching with ⟨f, hinjective, hsupported⟩
  exact ⟨⟨f, hinjective⟩⟩

end
end StatMech.FrontierD
