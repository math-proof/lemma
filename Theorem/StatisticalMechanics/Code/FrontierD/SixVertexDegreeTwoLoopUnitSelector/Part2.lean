/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoLoopUnitSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoLoopUnitSelector


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalDegreeTwoLoopUnitSelector.transitionBit_branches
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade}
    (selector : SixVertexHorizontalDegreeTwoLoopUnitSelector source)
    (dart : SixVertexOrientedDisagreementDart
      source.1.1.1.1 source.1.1.2.1) :
    sixVertexDegreeTwoSynchronizedComponentTransitionBit
        source.1.1.1.2.1 source.1.1.2.2.1 selector.hdegree
        selector.component (dart, false) =
      sixVertexDegreeTwoSynchronizedComponentTransitionBit
        source.1.1.1.2.1 source.1.1.2.2.1 selector.hdegree
        selector.component (dart, true) :=
  sixVertexDegreeTwoSynchronizedComponentTransitionBit_branches
    source.1.1.1.2.1 source.1.1.2.2.1 selector.hdegree
      selector.component dart


theorem SixVertexHorizontalDegreeTwoLoopUnitSelector.seamSum_eq_one
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade}
    (selector : SixVertexHorizontalDegreeTwoLoopUnitSelector source) :
    (∑ dart : SixVertexOrientedDisagreementDart
        source.1.1.1.1 source.1.1.2.1,
      if sixVertexDegreeTwoSynchronizedComponentSelector
          source.1.1.1.2.1 source.1.1.2.2.1 selector.hdegree
          selector.component dart then
        sixVertexDegreeTwoStrandStepSeamSign selector.hdegree dart
      else 0) = 1 :=
  sixVertexDegreeTwoSynchronizedComponentSelector_seamSum_eq_one
    source.1.1.1.2.1 source.1.1.2.2.1 selector.hdegree
      selector.component selector.charge

end
end StatMech.FrontierD
