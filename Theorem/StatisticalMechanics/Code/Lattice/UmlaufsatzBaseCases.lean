/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean -/

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
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem umBase_turnZ_right_iff (K : Set (Site 2)) (e : Dart)
    (h : e.head + (-rot90Fun e.dir) ∈ K) :
    turnZ K e = 1 ∧ (dartNext K e).dir = rot90Fun e.dir := by
  classical
  refine ⟨?_, (dartNext_front_head K e h).2⟩
  unfold turnZ; rw [if_pos h]


theorem umBase_turnZ_left_iff (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∉ K) :
    turnZ K e = -1 ∧ (dartNext K e).dir = -rot90Fun e.dir := by
  classical
  refine ⟨?_, dartNext_left_dir K e h1 h2⟩
  unfold turnZ; rw [if_neg h1, if_neg h2]


theorem umBase_turnZ_straight_iff (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∈ K) :
    turnZ K e = 0 ∧ (dartNext K e).dir = e.dir := by
  classical
  refine ⟨?_, dartNext_straight_dir K e h1 h2⟩
  unfold turnZ; rw [if_neg h1, if_pos h2]


theorem umBase_turnZ_determines_dir (K : Set (Site 2)) (e : Dart) :
    (dartNext K e).dir = rotPow (turn K e) e.dir :=
  dartNext_dir_eq_rotPow_turn K e


end Lattice
end StatMech
