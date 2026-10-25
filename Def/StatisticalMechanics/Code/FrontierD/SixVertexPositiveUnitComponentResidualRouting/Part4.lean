/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part2


namespace StatMech.FrontierD

noncomputable section

noncomputable def SixVertexPositiveUnitComponentResidualOrbitCover.ofTargetCoverage
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (physical : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt
      (SixVertexPositiveUnitComponentResidualSources T middle
        hmiddle_pos hmiddle_lt grade))
    (sourcePhysical : ∀ source,
      physical.sourcePhysical source =
        sixVertexHorizontalDegreeTwoHallSourcePhysicalEmbedding
          T middle hmiddle_pos hmiddle_lt grade source.1)
    (hcoverage :
      SixVertexPositiveUnitComponentResidualTargetCoverage physical) :
    SixVertexPositiveUnitComponentResidualOrbitCover T middle
      hmiddle_pos hmiddle_lt grade := by
  let lift := Classical.choice
    (positiveUnitComponentResidualTargetLift_nonempty physical hcoverage)
  exact
    { physical := physical
      sourcePhysical := sourcePhysical
      targetLift := lift.1
      targetLift_physical := lift.2 }

namespace SixVertexPositiveUnitComponentResidualOrbitCover

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


noncomputable def targetCoordinate
    (cover : SixVertexPositiveUnitComponentResidualOrbitCover T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexPositiveUnitComponentResidualSources T middle
        hmiddle_pos hmiddle_lt grade ↪
      Σ index, (cover.physical.data index).TargetLayer :=
  cover.physical.sourceCover.toEmbedding |>.trans
    ({
      toFun := fun source =>
        ⟨source.1,
          cover.physical.toAtlas.localMatching source.1 source.2⟩
      inj' := by
        rintro ⟨firstIndex, first⟩ ⟨secondIndex, second⟩ heq
        have hindex : firstIndex = secondIndex := congrArg Sigma.fst heq
        subst secondIndex
        have hfiber :
            cover.physical.toAtlas.localMatching firstIndex first =
              cover.physical.toAtlas.localMatching firstIndex second :=
          eq_of_heq (Sigma.mk.inj heq).2
        have hsource :=
          (cover.physical.toAtlas.localMatching firstIndex).injective hfiber
        cases hsource
        rfl } :
      (Σ index, (cover.physical.data index).SourceLayer) ↪
        Σ index, (cover.physical.data index).TargetLayer)


noncomputable def matching
    (cover : SixVertexPositiveUnitComponentResidualOrbitCover T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexPositiveUnitComponentResidualSources T middle
        hmiddle_pos hmiddle_lt grade ↪
      SixVertexHorizontalDegreeTwoHallTarget T middle
        hmiddle_pos hmiddle_lt grade :=
  cover.targetCoordinate.trans cover.targetLift


end SixVertexPositiveUnitComponentResidualOrbitCover
end
end StatMech.FrontierD
