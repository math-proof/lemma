/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

structure SixVertexDegreeTwoUnitComponentOrbitAtlas
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (Source : Type*) [Fintype Source] where
  sourcePhysical : Source ↪
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt
  Orbit : Type
  SourceOrbit : Orbit -> Type
  TargetOrbit : Orbit -> Type
  sourceOrbitPhysical : forall index, SourceOrbit index ->
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt
  targetOrbitPhysical : forall index, TargetOrbit index ->
    SixVertexConfigurationPhysicalTarget T middle
  localMatching : forall index, SourceOrbit index ↪ TargetOrbit index
  localMatching_related : forall index source,
    SixVertexDegreeTwoUnitStrandPhysicalRelated
      (sourceOrbitPhysical index source)
      (targetOrbitPhysical index (localMatching index source))
  sourceCover : Source ≃ Σ index, SourceOrbit index
  sourceCover_physical : forall source,
    sourceOrbitPhysical (sourceCover source).1 (sourceCover source).2 =
      sourcePhysical source
  targetEmbedding : (Σ index, TargetOrbit index) ↪
    SixVertexConfigurationPhysicalTarget T middle
  targetEmbedding_physical : forall index target,
    targetEmbedding ⟨index, target⟩ = targetOrbitPhysical index target

end
end StatMech.FrontierD
