/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

structure SixVertexPositiveUnitComponentOrbitCover
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (Source : Type*) [Fintype Source] where
  sourcePhysical : Source ↪
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt
  Orbit : Type
  data : Orbit → SixVertexPositiveUnitComponentOrbitData T middle
  sourceCover : Source ≃ Σ index, (data index).SourceLayer
  sourceCover_physical : ∀ source,
    (data (sourceCover source).1).base.sourceEmbedding
        hmiddle_pos hmiddle_lt (sourceCover source).2 =
      sourcePhysical source
  targetEmbedding : (Σ index, (data index).TargetLayer) ↪
    SixVertexConfigurationPhysicalTarget T middle
  targetEmbedding_physical : ∀ index target,
    targetEmbedding ⟨index, target⟩ =
      (data index).base.targetEmbedding target

end
end StatMech.FrontierD
