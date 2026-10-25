/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2


namespace StatMech.FrontierD

noncomputable section

attribute [instance]
  SixVertexHorizontalTwoCycleFiberReconnectionComponents.componentFintype


def SixVertexHorizontalTwoCycleActiveKeyComponentRouting.toActiveKeyFiberRouting
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalTwoCycleActiveKeyComponentRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalTwoCycleActiveKeyFiberRouting T middle
      hmiddle_pos hmiddle_lt grade where
  route := routing.route
  active_injective := routing.active_injective
  supported := routing.supported
  fiberEmbedding := fun key hkey => (routing.components key hkey).toEmbedding


def SixVertexHorizontalTwoCycleActiveKeyComponentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, Nonempty
    (SixVertexHorizontalTwoCycleActiveKeyComponentRouting T middle
      hmiddle_pos hmiddle_lt grade)


end
end StatMech.FrontierD
