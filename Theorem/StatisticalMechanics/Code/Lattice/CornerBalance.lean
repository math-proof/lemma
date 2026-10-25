/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.CornerBalance
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem totalTurnZ_eq_cornerBalance (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    totalTurnZ K e p = rightCornerCount K e p - leftCornerCount K e p := by
  classical
  unfold totalTurnZ rightCornerCount leftCornerCount
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases turnZ_mem K ((dartNext K)^[i] e) with h | h | h <;> rw [h] <;> norm_num


theorem turningIsFullRevolution_of_cornerBalance (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : rightCornerCount K a.1 (dartOrbitPeriod K a) -
          leftCornerCount K a.1 (dartOrbitPeriod K a) = 4 ∨
        rightCornerCount K a.1 (dartOrbitPeriod K a) -
          leftCornerCount K a.1 (dartOrbitPeriod K a) = -4) :
    TurningIsFullRevolution K a := by
  unfold TurningIsFullRevolution
  rw [totalTurnZ_eq_cornerBalance]
  exact h


theorem totalTurnZ_four_of_all_left (K : Set (Site 2)) (e : Dart)
    (h0 : turnZ K e = -1)
    (h1 : turnZ K (dartNext K e) = -1)
    (h2 : turnZ K ((dartNext K)^[2] e) = -1)
    (h3 : turnZ K ((dartNext K)^[3] e) = -1) :
    totalTurnZ K e 4 = -4 := by
  unfold totalTurnZ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, Function.iterate_zero_apply, Function.iterate_one]
  rw [h0, h1, h2, h3]
  ring


end Lattice
end StatMech
