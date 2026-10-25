/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem dmBase_isPeriodicPt : Function.IsPeriodicPt (dartNextSub domino) 6 dmBase := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  apply Subtype.ext
  rw [dartNextSub_iterate_val]
  exact iterate_dmD_6


theorem dmBase_not_periodic_two :
    ¬ Function.IsPeriodicPt (dartNextSub domino) 2 dmBase := by
  intro h
  have h2 : (dartNext domino)^[2] dmD0 = dmD0 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_iterate_val] at this
  rw [iterate_dmD_2] at h2
  have hd : dmD2.dir = dmD0.dir := congrArg Dart.dir h2
  rw [dmD2_dir, dmD0_dir] at hd
  have := congrFun hd 1; simp at this


theorem dmBase_not_periodic_three :
    ¬ Function.IsPeriodicPt (dartNextSub domino) 3 dmBase := by
  intro h
  have h3 : (dartNext domino)^[3] dmD0 = dmD0 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_iterate_val] at this
  rw [iterate_dmD_3] at h3
  have hd : dmD3.dir = dmD0.dir := congrArg Dart.dir h3
  rw [dmD3_dir, dmD0_dir] at hd
  have := congrFun hd 1; simp at this


theorem dmBase_not_fixedPt : ¬ Function.IsFixedPt (dartNextSub domino) dmBase := by
  intro h
  have h1 : dartNext domino dmD0 = dmD0 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_val] at this
  rw [dartNext_dmD0] at h1
  have hd : dmD1.dir = dmD0.dir := congrArg Dart.dir h1
  rw [dmD1_dir, dmD0_dir] at hd
  have := congrFun hd 0; simp at this


theorem domino_orbitPeriod_eq_six : dartOrbitPeriod domino dmBase = 6 := by
  unfold dartOrbitPeriod
  have hdvd : Function.minimalPeriod (dartNextSub domino) dmBase ∣ 6 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp dmBase_isPeriodicPt
  have hper : Function.IsPeriodicPt (dartNextSub domino)
      (Function.minimalPeriod (dartNextSub domino) dmBase) dmBase :=
    Function.isPeriodicPt_minimalPeriod _ _
  set m := Function.minimalPeriod (dartNextSub domino) dmBase with hm
  have hmem : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases m <;> omega
  rcases hmem with h | h | h | h
  · rw [h] at hper
    rw [Function.IsPeriodicPt, Function.iterate_one] at hper
    exact absurd hper dmBase_not_fixedPt
  · rw [h] at hper; exact absurd hper dmBase_not_periodic_two
  · rw [h] at hper; exact absurd hper dmBase_not_periodic_three
  · exact h


theorem domino_turningIsFullRevolution :
    TurningIsFullRevolution domino dmBase := by
  unfold TurningIsFullRevolution
  rw [show (dmBase).1 = dmD0 from rfl, domino_orbitPeriod_eq_six]
  right
  exact domino_totalTurnZ_six


theorem domino_simplePolygonCornerBalance :
    SimplePolygonCornerBalance domino dmBase :=
  (simplePolygonCornerBalance_iff domino dmBase).mpr domino_turningIsFullRevolution

end Lattice
end StatMech
