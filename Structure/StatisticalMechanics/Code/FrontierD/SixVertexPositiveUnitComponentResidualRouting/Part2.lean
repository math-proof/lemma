/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part2


namespace StatMech.FrontierD

noncomputable section

structure SixVertexPositiveUnitComponentResidualOrbitCover
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  physical : SixVertexPositiveUnitComponentOrbitCover T middle
    hmiddle_pos hmiddle_lt
    (SixVertexPositiveUnitComponentResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
  sourcePhysical : ∀ source,
    physical.sourcePhysical source =
      sixVertexHorizontalDegreeTwoHallSourcePhysicalEmbedding
        T middle hmiddle_pos hmiddle_lt grade source.1
  targetLift : (Σ index, (physical.data index).TargetLayer) ↪
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade
  targetLift_physical : ∀ index target,
    sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
        T middle hmiddle_pos hmiddle_lt grade
        (targetLift ⟨index, target⟩) =
      physical.targetEmbedding ⟨index, target⟩


end
end StatMech.FrontierD
