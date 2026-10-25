/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexDegreeTwoUnitComponentOrbitAtlas

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Source : Type*} [Fintype Source]


theorem matching_related
    (atlas : SixVertexDegreeTwoUnitComponentOrbitAtlas T middle
      hmiddle_pos hmiddle_lt Source) (source : Source) :
    atlas.Related source (atlas.matching source) := by
  let covered := atlas.sourceCover source
  have hlocal := atlas.localMatching_related covered.1 covered.2
  unfold Related
  rw [← atlas.sourceCover_physical source]
  change SixVertexDegreeTwoUnitStrandPhysicalRelated
    (atlas.sourceOrbitPhysical covered.1 covered.2)
    (atlas.matching source)
  rw [show atlas.matching source =
      atlas.targetEmbedding
        ⟨covered.1, atlas.localMatching covered.1 covered.2⟩ by rfl,
    atlas.targetEmbedding_physical]
  exact hlocal


theorem hall
    (atlas : SixVertexDegreeTwoUnitComponentOrbitAtlas T middle
      hmiddle_pos hmiddle_lt Source) :
    forall sources : Finset Source,
      sources.card <=
        (Finset.univ.filter fun target :
            SixVertexConfigurationPhysicalTarget T middle =>
          ∃ source ∈ sources, atlas.Related source target).card := by
  exact (Fintype.all_card_le_filter_rel_iff_exists_injective atlas.Related).2
    ⟨atlas.matching, atlas.matching.injective, atlas.matching_related⟩

end SixVertexDegreeTwoUnitComponentOrbitAtlas
end
end StatMech.FrontierD
