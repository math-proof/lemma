/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzBaseCases.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzEar.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnetEar
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzClose.Part4
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

@[simp] theorem uc_rotSub_val (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (uc_rotSub K a).1 = uc_rotDart a.1 := rfl


theorem uc_isPeriodicPt_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    Function.IsPeriodicPt (dartNextSub (uc_rotSet K)) n (uc_rotSub K a) ↔
      Function.IsPeriodicPt (dartNextSub K) n a := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  constructor
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    show ((dartNextSub K)^[n] a).1 = a.1
    rw [dartNextSub_iterate_val]
    have hstep : (dartNext (uc_rotSet K))^[n] (uc_rotSub K a).1
        = uc_rotDart ((dartNext K)^[n] a.1) := by
      show (dartNext (uc_rotSet K))^[n] (uc_rotDart a.1) = _
      rw [uc_iterate_dartNext_rot]
    rw [hstep] at hv
    exact uc_rotDart_injective hv
  · intro h
    apply Subtype.ext
    rw [dartNextSub_iterate_val]
    show (dartNext (uc_rotSet K))^[n] (uc_rotDart a.1) = uc_rotDart a.1
    rw [uc_iterate_dartNext_rot]
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    rw [hv]


theorem uc_dartOrbitPeriod_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    dartOrbitPeriod (uc_rotSet K) (uc_rotSub K a) = dartOrbitPeriod K a := by
  unfold dartOrbitPeriod
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  exact uc_isPeriodicPt_rot K a n


theorem uc_cornerBalance_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance (uc_rotSet K) (uc_rotSub K a) = cornerBalance K a := by
  unfold cornerBalance
  rw [uc_rotSub_val, uc_dartOrbitPeriod_rot, uc_rightCornerCount_rot, uc_leftCornerCount_rot]


theorem uc_totalTurnZ_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ (uc_rotSet K) (uc_rotSub K a).1 (dartOrbitPeriod (uc_rotSet K) (uc_rotSub K a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  rw [← cornerBalance_eq_totalTurnZ, ← cornerBalance_eq_totalTurnZ, uc_cornerBalance_rot]


theorem uc_turningIsFullRevolution_rot (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    TurningIsFullRevolution (uc_rotSet K) (uc_rotSub K a) := by
  unfold TurningIsFullRevolution at h ⊢
  rw [uc_totalTurnZ_rot]
  exact h


theorem uc_rotSet_domino : uc_rotSet domino = {![0, 0], ![0, 1]} := by
  unfold uc_rotSet domino
  rw [Set.image_insert_eq, Set.image_singleton,
      show rot90Fun (![0, 0] : Site 2) = ![0, 0] by
        rw [rot90Fun_apply]; funext i; fin_cases i <;> simp,
      show rot90Fun (![1, 0] : Site 2) = ![0, 1] by
        rw [rot90Fun_apply]; funext i; fin_cases i <;> simp]


theorem uc_verticalDomino_totalTurn_eq_four :
    totalTurnZ (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = 4 ∨
      totalTurnZ (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = -4 := by
  rw [uc_totalTurnZ_rot]
  exact domino_turningIsFullRevolution

open Real in


theorem uc_verticalDomino_totalTurnAngle_eq_two_pi :
    totalTurnAngle (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = 2 * Real.pi ∨
      totalTurnAngle (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = -(2 * Real.pi) := by
  rw [umBase_totalTurnAngle_eq]
  rcases uc_verticalDomino_totalTurn_eq_four with h | h
  · left; rw [h]; push_cast; ring
  · right; rw [h]; push_cast; ring


end Lattice
end StatMech
