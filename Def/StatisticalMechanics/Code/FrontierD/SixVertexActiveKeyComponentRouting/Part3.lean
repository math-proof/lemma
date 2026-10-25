/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part3


namespace StatMech.FrontierD

noncomputable section

attribute [instance]
  SixVertexHorizontalTwoCycleFiberReconnectionComponents.componentFintype


attribute [instance]
  SixVertexHorizontalTwoCycleTokenReconnectionComponents.componentFintype


def SixVertexHorizontalTwoCycleTokenReconnectionComponents.toSupportedMatching
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (components : SixVertexHorizontalTwoCycleTokenReconnectionComponents
      T middle hmiddle_pos hmiddle_lt grade) :
    exists matching :
      SixVertexHorizontalActualDeficitTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
        SixVertexHorizontalActualSurplusTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle,
      Function.Injective matching /\
        forall source,
          sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
            hmiddle_pos hmiddle_lt grade source (matching source) := by
  refine ⟨components.reconnect, ?_, components.supported⟩
  intro first second heq
  exact components.injective_within_component first second
    (components.output_recovers_component first second heq) heq


def SixVertexHorizontalTwoCycleTokenComponentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, Nonempty
    (SixVertexHorizontalTwoCycleTokenReconnectionComponents T middle
      hmiddle_pos hmiddle_lt grade)


end
end StatMech.FrontierD
