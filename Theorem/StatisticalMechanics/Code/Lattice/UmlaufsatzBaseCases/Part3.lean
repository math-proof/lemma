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
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzBaseCases.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

open Real in


theorem umBase_totalTurnAngle_eq (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    totalTurnAngle K e p = (totalTurnZ K e p : ℝ) * (Real.pi / 2) := by
  unfold totalTurnAngle turnAngle totalTurnZ
  rw [← Finset.sum_mul]
  push_cast
  rfl


theorem umBase_square_turnCount : totalTurnZ unitCell ucDart0 4 = -4 :=
  unitCell_totalTurnZ_four

open Real in


theorem umBase_square_turning : totalTurnAngle unitCell ucDart0 4 = -(2 * Real.pi) := by
  rw [umBase_totalTurnAngle_eq, umBase_square_turnCount]
  push_cast
  ring

open Real in


theorem umBase_square_turning_period :
    totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -(2 * Real.pi) := by
  rw [show (ucBase).1 = ucDart0 from rfl, unitCell_orbitPeriod_eq_four]
  exact umBase_square_turning


theorem umBase_square_rightCount : rightCornerCount unitCell ucDart0 4 = 0 := by
  classical
  unfold rightCornerCount
  rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  simp only [Finset.mem_range] at hi
  
  interval_cases i
  · rw [Function.iterate_zero_apply, ucDart0_turnZ]; decide
  · rw [iterate_ucDart_1, ucDart1_turnZ]; decide
  · rw [iterate_ucDart_2, ucDart2_turnZ]; decide
  · rw [iterate_ucDart_3, ucDart3_turnZ]; decide


theorem umBase_square_leftCount : leftCornerCount unitCell ucDart0 4 = 4 := by
  classical
  unfold leftCornerCount
  have hfilter : (Finset.range 4).filter
      (fun i => turnZ unitCell ((dartNext unitCell)^[i] ucDart0) = -1) = Finset.range 4 := by
    rw [Finset.filter_eq_self]
    intro i hi
    simp only [Finset.mem_range] at hi
    interval_cases i
    · rw [Function.iterate_zero_apply]; exact ucDart0_turnZ
    · rw [iterate_ucDart_1]; exact ucDart1_turnZ
    · rw [iterate_ucDart_2]; exact ucDart2_turnZ
    · rw [iterate_ucDart_3]; exact ucDart3_turnZ
  rw [hfilter]
  simp


theorem umBase_cornerBalance :
    leftCornerCount unitCell ucDart0 4 - rightCornerCount unitCell ucDart0 4 = 4 := by
  rw [umBase_square_leftCount, umBase_square_rightCount]; ring


theorem umBase_cornerBalance_pm :
    leftCornerCount unitCell ucDart0 4 - rightCornerCount unitCell ucDart0 4 = 4 ∨
    leftCornerCount unitCell ucDart0 4 - rightCornerCount unitCell ucDart0 4 = -4 :=
  Or.inl umBase_cornerBalance


theorem umBase_cornerBalance_eq_neg_turnCount :
    leftCornerCount unitCell ucDart0 4 - rightCornerCount unitCell ucDart0 4
      = -(totalTurnZ unitCell ucDart0 4) := by
  rw [totalTurnZ_eq_cornerBalance]
  ring


theorem umBase_domino_rightCount : rightCornerCount domino dmD0 6 = 0 := by
  classical
  unfold rightCornerCount
  rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  simp only [Finset.mem_range] at hi
  interval_cases i
  · rw [Function.iterate_zero_apply, dmD0_turnZ]; decide
  · rw [iterate_dmD_1, dmD1_turnZ]; decide
  · rw [iterate_dmD_2, dmD2_turnZ]; decide
  · rw [iterate_dmD_3, dmD3_turnZ]; decide
  · rw [iterate_dmD_4, dmD4_turnZ]; decide
  · rw [iterate_dmD_5, dmD5_turnZ]; decide


theorem umBase_domino_leftCount : leftCornerCount domino dmD0 6 = 4 := by
  classical
  unfold leftCornerCount
  have hcard : ((Finset.range 6).filter
      (fun i => turnZ domino ((dartNext domino)^[i] dmD0) = -1)).card = 4 := by
    rw [Finset.card_filter]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [Function.iterate_zero_apply, dmD0_turnZ, iterate_dmD_1, dmD1_turnZ,
      iterate_dmD_2, dmD2_turnZ, iterate_dmD_3, dmD3_turnZ, iterate_dmD_4, dmD4_turnZ,
      iterate_dmD_5, dmD5_turnZ]
    decide
  rw [hcard]; rfl


theorem umBase_domino_cornerBalance :
    leftCornerCount domino dmD0 6 - rightCornerCount domino dmD0 6 = 4 := by
  rw [umBase_domino_leftCount, umBase_domino_rightCount]; ring

open Real in


theorem umBase_domino_turning : totalTurnAngle domino dmD0 6 = -(2 * Real.pi) := by
  rw [umBase_totalTurnAngle_eq, domino_totalTurnZ_six]
  push_cast
  ring

end Lattice
end StatMech
