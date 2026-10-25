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
import Def.StatisticalMechanics.Code.Lattice.EarRemoval
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem orbitStep_partition (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    rightCornerCount K e p + straightStepCount K e p + leftCornerCount K e p = (p : ℤ) := by
  classical
  unfold rightCornerCount straightStepCount leftCornerCount
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [show ((p : ℤ)) = ∑ _i ∈ Finset.range p, (1 : ℤ) by simp]
  apply Finset.sum_congr rfl
  intro i _
  rcases turnZ_mem K ((dartNext K)^[i] e) with h | h | h <;> rw [h] <;> norm_num


theorem totalTurnZ_eq_rl (K : Set (Site 2)) (e : Dart) (p : ℕ) {r l : ℤ}
    (hr : rightCornerCount K e p = r) (hl : leftCornerCount K e p = l) :
    totalTurnZ K e p = r - l := by
  rw [totalTurnZ_eq_cornerBalance, hr, hl]


theorem totalTurnZ_neg_four_of_convex (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hr : rightCornerCount K e p = 0) (hl : leftCornerCount K e p = 4) :
    totalTurnZ K e p = -4 := by
  rw [totalTurnZ_eq_rl K e p hr hl]; ring


theorem totalTurnZ_four_of_reflexFree (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hr : rightCornerCount K e p = 4) (hl : leftCornerCount K e p = 0) :
    totalTurnZ K e p = 4 := by
  rw [totalTurnZ_eq_rl K e p hr hl]; ring


theorem turningIsFullRevolution_of_corner_diff_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : rightCornerCount K a.1 (dartOrbitPeriod K a) -
          leftCornerCount K a.1 (dartOrbitPeriod K a) = 4 ∨
        rightCornerCount K a.1 (dartOrbitPeriod K a) -
          leftCornerCount K a.1 (dartOrbitPeriod K a) = -4) :
    TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_cornerBalance K a h


theorem turningIsFullRevolution_of_canonical_convex (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hr : rightCornerCount K a.1 (dartOrbitPeriod K a) = 0)
    (hl : leftCornerCount K a.1 (dartOrbitPeriod K a) = 4) :
    TurningIsFullRevolution K a := by
  apply turningIsFullRevolution_of_corner_diff_four
  right; rw [hr, hl]; ring


theorem turningIsFullRevolution_of_canonical_reflexFree (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hr : rightCornerCount K a.1 (dartOrbitPeriod K a) = 4)
    (hl : leftCornerCount K a.1 (dartOrbitPeriod K a) = 0) :
    TurningIsFullRevolution K a := by
  apply turningIsFullRevolution_of_corner_diff_four
  left; rw [hr, hl]; ring


theorem earTurnReplacement (K K' : Set (Site 2)) (e e' : Dart) (p p' : ℕ)
    {r l r' l' : ℤ}
    (hr : rightCornerCount K e p = r) (hl : leftCornerCount K e p = l)
    (hr' : rightCornerCount K' e' p' = r') (hl' : leftCornerCount K' e' p' = l')
    (hbal : r - l = r' - l') :
    totalTurnZ K e p = totalTurnZ K' e' p' := by
  rw [totalTurnZ_eq_rl K e p hr hl, totalTurnZ_eq_rl K' e' p' hr' hl', hbal]


theorem turningIsFullRevolution_of_balance_eq_base (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hbase : rightCornerCount K a.1 (dartOrbitPeriod K a) -
        leftCornerCount K a.1 (dartOrbitPeriod K a) =
      rightCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) -
        leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)) :
    TurningIsFullRevolution K a := by
  apply turningIsFullRevolution_of_corner_diff_four
  right
  
  have hbal : rightCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) -
      leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
    have h := unitCell_totalTurnZ_four
    rw [show (ucBase).1 = ucDart0 from rfl] at *
    rw [unitCell_orbitPeriod_eq_four] at hbase ⊢
    rw [← totalTurnZ_eq_cornerBalance]
    exact h
  rw [hbase, hbal]


end Lattice
end StatMech
