/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def
    SixVertexHorizontalDegreeTwoHighChargeHallRouting.toTokenComponents
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalTwoCycleTokenReconnectionComponents T middle
      hmiddle_pos hmiddle_lt grade where
  Component := Bool
  componentFintype := inferInstance
  sourceComponent source :=
    decide (sixVertexHorizontalDegreeTwoHighCharge source)
  reconnect := routing.reconnect
  supported := routing.reconnect_supported
  output_recovers_component first second heq := by
    rw [routing.reconnect_injective heq]
  injective_within_component first second _ heq :=
    routing.reconnect_injective heq

def SixVertexHorizontalDegreeTwoHighChargeHallRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty
    (SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)


end
end StatMech.FrontierD
