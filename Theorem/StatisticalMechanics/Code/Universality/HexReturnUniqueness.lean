/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Def.StatisticalMechanics.Code.Universality.HexReturnUniqueness


namespace StatMech.Universality

open Complex HexWalk


namespace HexReturnCoord

@[simp] theorem value_zero : zero.value = 0 := by
  simp [zero, value]

@[simp] theorem value_base : base.value = 1 := by
  simp [base, value]

@[simp] theorem value_negBase : negBase.value = -1 := by
  simp [negBase, value]

theorem value_add (d e : HexReturnCoord) : (d.add e).value = d.value + e.value := by
  unfold add value
  push_cast
  ring


theorem value_left (d : HexReturnCoord) :
    d.left.value = -(hexOmega ^ 2 * d.value) := by
  unfold left value
  push_cast
  ring_nf
  rw [hexConcrete_omega_cubic]
  have h3 : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
  rw [h3]
  ring


theorem value_right (d : HexReturnCoord) :
    d.right.value = -(hexOmega * d.value) := by
  unfold right value
  push_cast
  ring_nf
  rw [hexConcrete_omega_cubic]
  ring


end HexReturnCoord
end StatMech.Universality
