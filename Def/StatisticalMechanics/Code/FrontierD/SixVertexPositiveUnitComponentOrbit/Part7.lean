/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part3
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitCover

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Source : Type*} [Fintype Source]


noncomputable def toAtlas
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) :
    SixVertexDegreeTwoUnitComponentOrbitAtlas T middle
      hmiddle_pos hmiddle_lt Source where
  sourcePhysical := cover.sourcePhysical
  Orbit := cover.Orbit
  SourceOrbit := fun index => (cover.data index).SourceLayer
  TargetOrbit := fun index => (cover.data index).TargetLayer
  sourceOrbitPhysical := fun index source =>
    (cover.data index).base.sourceEmbedding hmiddle_pos hmiddle_lt source
  targetOrbitPhysical := fun index target =>
    (cover.data index).base.targetEmbedding target
  localMatching := fun index =>
    ((cover.data index).base.presentation
      hmiddle_pos hmiddle_lt).booleanMatching
  localMatching_related := fun index source =>
    ((cover.data index).base.presentation
      hmiddle_pos hmiddle_lt).booleanMatching_related source
  sourceCover := cover.sourceCover
  sourceCover_physical := cover.sourceCover_physical
  targetEmbedding := cover.targetEmbedding
  targetEmbedding_physical := cover.targetEmbedding_physical


noncomputable def matching
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) :
    Source ↪ SixVertexConfigurationPhysicalTarget T middle :=
  cover.toAtlas.matching


end SixVertexPositiveUnitComponentOrbitCover
end
end StatMech.FrontierD
