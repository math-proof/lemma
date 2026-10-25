/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectBarrierRightStrip.Part2


namespace StatMech.FrontierD

noncomputable section

theorem fkRectSetConnectionWithinEvent_isIncreasing
    (R : FKRectTorus) (T X Y : Set R.Vertex) :
    IsIncreasing (fkRectSetConnectionWithinEvent R T X Y) := by
  intro omega tau hot
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy, hxy.mono_configuration R hot T⟩

theorem fkRectNoLeftStripCrossingEvent_isDecreasing
    (R : FKRectTorus) (right : Nat) :
    IsDecreasing (fkRectNoLeftStripCrossingEvent R right) := by
  exact (fkRectSetConnectionWithinEvent_isIncreasing R
    (fkRectLeftStrip R right) (fkRectColumnSet R 0)
    (fkRectColumnSet R right)).compl

theorem fkRectNoLeftStripCrossing_dependsOnOutsideRightStripBand
    (R : FKRectTorus) (leftRight cut lower upper : Nat)
    (hsep : leftRight < cut) :
    FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut lower upper)
      (fkRectNoLeftStripCrossingEvent R leftRight) := by
  apply FKRectDependsOnOutsideRegion.compl
  apply fkRectSetConnectionWithinEvent_dependsOnOutsideRegion
  intro v hvT hvS
  exact (not_lt_of_ge (hvS.1.trans hvT)) hsep


end
end StatMech.FrontierD
