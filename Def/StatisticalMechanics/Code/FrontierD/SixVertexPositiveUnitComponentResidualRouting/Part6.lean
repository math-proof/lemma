/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part4


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHorizontalHallTargetCanonicalLoop
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade := by
  let physical := sixVertexHorizontalActualSurplusConfigurationPair target
  let firstPairing : SixVertexCompatibleLoopPairing physical.1.1.1 :=
    ⟨fun vertex =>
        sixVertexPreferredCompatiblePairing physical.1.1.1 vertex,
      sixVertexPreferredCompatiblePairing_compatible
        physical.1.1.1 physical.1.1.2.1⟩
  let secondPairing : SixVertexCompatibleLoopPairing physical.1.2.1 :=
    ⟨fun vertex =>
        sixVertexPreferredCompatiblePairing physical.1.2.1 vertex,
      sixVertexPreferredCompatiblePairing_compatible
        physical.1.2.1 physical.1.2.2.1⟩
  refine ⟨⟨physical.1, firstPairing, secondPairing⟩, ?_⟩
  rw [sixVertexLoopDecoratedPairBigrade_eq_configurationPair]
  exact physical.2

end
end StatMech.FrontierD
