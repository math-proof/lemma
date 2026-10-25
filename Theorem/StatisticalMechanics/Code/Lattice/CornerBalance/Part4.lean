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
import Def.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem ucBase_isPeriodicPt : Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  apply Subtype.ext
  rw [dartNextSub_iterate_val]
  exact iterate_ucDart_4


theorem ucBase_not_fixedPt : ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase := by
  intro h
  have h2 : dartNext unitCell ucDart0 = ucDart0 := by
    have := congrArg Subtype.val h
    rwa [dartNextSub_val] at this
  rw [dartNext_ucDart0] at h2
  have hd : ucDart1.dir = ucDart0.dir := congrArg Dart.dir h2
  rw [ucDart1_dir, ucDart0_dir] at hd
  have := congrFun hd 0
  simp at this


theorem ucBase_not_periodic_two :
    ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase := by
  intro h
  have h2 : (dartNext unitCell)^[2] ucDart0 = ucDart0 := by
    have := congrArg Subtype.val h
    rwa [dartNextSub_iterate_val] at this
  rw [iterate_ucDart_2] at h2
  have hd : ucDart2.dir = ucDart0.dir := congrArg Dart.dir h2
  rw [ucDart2_dir, ucDart0_dir] at hd
  have := congrFun hd 0
  simp at this


theorem unitCell_orbitPeriod_eq_four : dartOrbitPeriod unitCell ucBase = 4 := by
  unfold dartOrbitPeriod
  have hdvd : Function.minimalPeriod (dartNextSub unitCell) ucBase ∣ 4 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ucBase_isPeriodicPt
  have hper : Function.IsPeriodicPt (dartNextSub unitCell)
      (Function.minimalPeriod (dartNextSub unitCell) ucBase) ucBase :=
    Function.isPeriodicPt_minimalPeriod _ _
  set m := Function.minimalPeriod (dartNextSub unitCell) ucBase with hm
  have hmem : m = 1 ∨ m = 2 ∨ m = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases m <;> omega
  rcases hmem with h | h | h
  · rw [h] at hper
    rw [Function.IsPeriodicPt, Function.iterate_one] at hper
    exact absurd hper ucBase_not_fixedPt
  · rw [h] at hper; exact absurd hper ucBase_not_periodic_two
  · exact h


theorem unitCell_turningIsFullRevolution :
    TurningIsFullRevolution unitCell ucBase := by
  unfold TurningIsFullRevolution
  rw [show (ucBase).1 = ucDart0 from rfl, unitCell_orbitPeriod_eq_four]
  right
  exact unitCell_totalTurnZ_four


theorem unitCell_orbitPeriod_ge_four : 4 ≤ dartOrbitPeriod unitCell ucBase :=
  orbitPeriod_ge_four_of_fullRevolution unitCell ucBase unitCell_turningIsFullRevolution

end Lattice
end StatMech
