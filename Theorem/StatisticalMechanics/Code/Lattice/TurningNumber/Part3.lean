/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.TurningNumber.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem turnZ_mem (K : Set (Site 2)) (e : Dart) :
    turnZ K e = 1 ∨ turnZ K e = 0 ∨ turnZ K e = -1 := by
  classical
  unfold turnZ
  split_ifs <;> simp


theorem abs_turnZ_le_one (K : Set (Site 2)) (e : Dart) : |turnZ K e| ≤ 1 := by
  rcases turnZ_mem K e with h | h | h <;> rw [h] <;> decide


theorem turnZ_cast_eq_turn (K : Set (Site 2)) (e : Dart) :
    ((turnZ K e : ℤ) : ZMod 4) = turn K e := by
  classical
  unfold turnZ turn
  split_ifs <;> decide


theorem dartNext_dir_eq_rotPow_turn (K : Set (Site 2)) (e : Dart) :
    (dartNext K e).dir = rotPow (turn K e) e.dir := by
  classical
  unfold turn
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [if_pos hA, (dartNext_front_head K e hA).2]; rfl
  · rw [if_neg hA]
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [if_pos hB, dartNext_straight_dir K e hA hB]; rfl
    · rw [if_neg hB, dartNext_left_dir K e hA hB, rotPow_three]


end Lattice
end StatMech
