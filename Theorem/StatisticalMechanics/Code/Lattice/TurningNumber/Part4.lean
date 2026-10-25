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
import Def.StatisticalMechanics.Code.Lattice.TurningNumber.Part3
open SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem cumTurn_zero (K : Set (Site 2)) (e : Dart) : cumTurn K e 0 = 0 := by
  simp [cumTurn]


theorem cumTurn_succ (K : Set (Site 2)) (e : Dart) (k : ℕ) :
    cumTurn K e (k + 1) = turn K ((dartNext K)^[k] e) + cumTurn K e k := by
  unfold cumTurn; rw [Finset.sum_range_succ]; ring


theorem dir_iterate_eq_rotPow_cumTurn (K : Set (Site 2)) (e : Dart) (k : ℕ) :
    ((dartNext K)^[k] e).dir = rotPow (cumTurn K e k) e.dir := by
  induction k with
  | zero => rw [cumTurn_zero, rotPow_zero, Function.iterate_zero_apply]
  | succ n ih =>
    rw [Function.iterate_succ_apply', dartNext_dir_eq_rotPow_turn, ih, cumTurn_succ,
      rotPow_add]


end Lattice
end StatMech
