/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Def.StatisticalMechanics.Code.Lattice.EarExistence
open SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem leftDart_tail (c : Site 2) : (leftDart c).tail = c := rfl

theorem leftDart_dir (c : Site 2) : (leftDart c).dir = ![-1, 0] := by
  rw [leftDart, mkDart_dir]

theorem leftDart_head (c : Site 2) : (leftDart c).head = c + ![-1, 0] := by
  rw [leftDart, mkDart_head]


theorem leftDart_travel (c : Site 2) : -rot90Fun (leftDart c).dir = ![0, 1] := by
  rw [leftDart_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp


theorem leftDart_head_coord0 (c : Site 2) : (leftDart c).head 0 = c 0 - 1 := by
  rw [leftDart_head, Pi.add_apply]; simp; ring


theorem leftDart_head_coord1 (c : Site 2) : (leftDart c).head 1 = c 1 := by
  rw [leftDart_head, Pi.add_apply]; simp


theorem leftDart_front_coord0 (c : Site 2) :
    ((leftDart c).head + (-rot90Fun (leftDart c).dir)) 0 = c 0 - 1 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_head_coord0]; simp


theorem leftDart_front_coord1 (c : Site 2) :
    ((leftDart c).head + (-rot90Fun (leftDart c).dir)) 1 = c 1 + 1 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_head_coord1]; simp


theorem leftDart_side_coord0 (c : Site 2) :
    ((leftDart c).tail + (-rot90Fun (leftDart c).dir)) 0 = c 0 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_tail]; simp


theorem leftDart_side_coord1 (c : Site 2) :
    ((leftDart c).tail + (-rot90Fun (leftDart c).dir)) 1 = c 1 + 1 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_tail]; simp


end Lattice
end StatMech
