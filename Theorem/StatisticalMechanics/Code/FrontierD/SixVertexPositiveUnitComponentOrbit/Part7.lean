/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitCover

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Source : Type*} [Fintype Source]


theorem matching_related
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) (source : Source) :
    (cover.toAtlas).Related source (cover.matching source) :=
  (cover.toAtlas).matching_related source


theorem matching_fineRelated
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) (source : Source) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((cover.sourcePhysical source).1.1,
        (cover.sourcePhysical source).2.1)
      ((cover.matching source).1.1, (cover.matching source).2.1) :=
  (cover.matching_related source).fineRelated


theorem matching_layers_ne
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) (source : Source) :
    (cover.matching source).1 ≠ (cover.matching source).2 :=
  SixVertexDegreeTwoUnitStrandPhysicalRelated.layers_ne
    (cover.matching_related source)


theorem matching_totalC
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) (source : Source) :
    sixVertexConfigurationPairTotalCPhysical (cover.sourcePhysical source) =
      sixVertexConfigurationPairTotalCPhysical (cover.matching source) := by
  exact sixVertexPairAtMostTwoCycleFineRelated_totalC
    (cover.matching_fineRelated source)


theorem hall
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) :
    ∀ sources : Finset Source,
      sources.card ≤
        (Finset.univ.filter fun target :
            SixVertexConfigurationPhysicalTarget T middle =>
          ∃ source ∈ sources,
            (cover.toAtlas).Related source target).card :=
  cover.toAtlas.hall

end SixVertexPositiveUnitComponentOrbitCover
end
end StatMech.FrontierD
