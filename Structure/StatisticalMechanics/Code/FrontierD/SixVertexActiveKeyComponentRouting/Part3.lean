/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting


namespace StatMech.FrontierD

noncomputable section

attribute [instance]
  SixVertexHorizontalTwoCycleFiberReconnectionComponents.componentFintype


structure SixVertexHorizontalTwoCycleTokenReconnectionComponents
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  Component : Type
  componentFintype : Fintype Component
  sourceComponent :
    SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
        Component
  reconnect :
    SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
      SixVertexHorizontalActualSurplusTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
  supported : forall source,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source (reconnect source)
  output_recovers_component : forall first second,
    reconnect first = reconnect second ->
      sourceComponent first = sourceComponent second
  injective_within_component : forall first second,
    sourceComponent first = sourceComponent second ->
      reconnect first = reconnect second -> first = second

end
end StatMech.FrontierD
