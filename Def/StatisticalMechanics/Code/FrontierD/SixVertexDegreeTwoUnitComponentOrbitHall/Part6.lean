/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexDegreeTwoUnitComponentOrbitAtlas

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Source : Type*} [Fintype Source]


def Related
    (atlas : SixVertexDegreeTwoUnitComponentOrbitAtlas T middle
      hmiddle_pos hmiddle_lt Source)
    (source : Source) (target : SixVertexConfigurationPhysicalTarget T middle) :
    Prop :=
  SixVertexDegreeTwoUnitStrandPhysicalRelated
    (atlas.sourcePhysical source) target


noncomputable def matching
    (atlas : SixVertexDegreeTwoUnitComponentOrbitAtlas T middle
      hmiddle_pos hmiddle_lt Source) :
    Source ↪ SixVertexConfigurationPhysicalTarget T middle :=
  atlas.sourceCover.toEmbedding |>.trans
    ({
      toFun := fun source =>
        ⟨source.1, atlas.localMatching source.1 source.2⟩
      inj' := by
        rintro ⟨firstIndex, first⟩ ⟨secondIndex, second⟩ heq
        have hindex : firstIndex = secondIndex := congrArg Sigma.fst heq
        subst secondIndex
        have hfiber :
            atlas.localMatching firstIndex first =
              atlas.localMatching firstIndex second := by
          exact eq_of_heq (Sigma.mk.inj heq).2
        have := (atlas.localMatching firstIndex).injective hfiber
        cases this
        rfl } :
      (Σ index, atlas.SourceOrbit index) ↪
        (Σ index, atlas.TargetOrbit index)) |>.trans
    atlas.targetEmbedding

end SixVertexDegreeTwoUnitComponentOrbitAtlas
end
end StatMech.FrontierD
