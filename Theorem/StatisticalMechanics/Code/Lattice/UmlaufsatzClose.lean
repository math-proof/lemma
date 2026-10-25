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
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzClose
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem uc_totalTurn_eq_four_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hmax : uc_WindsAtMostOnce K a) (hmin : uc_WindsAtLeastOnce K a) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 := by
  have hdvd := four_dvd_orbit_totalTurnZ K a
  unfold uc_WindsAtMostOnce at hmax
  unfold uc_WindsAtLeastOnce at hmin
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hmax hmin ⊢
  rw [abs_le] at hmax
  have hk1 : k = 1 ∨ k = -1 := by
    rcases lt_trichotomy k 0 with h | h | h
    · right; omega
    · exact absurd (by rw [h]; ring) hmin
    · left; omega
  rcases hk1 with h | h
  · left; rw [h]; ring
  · right; rw [h]; ring


theorem uc_winds_of_totalTurn_eq_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) :
    uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a := by
  unfold uc_WindsAtMostOnce uc_WindsAtLeastOnce
  rcases h with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩


theorem uc_winds_iff (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a) ↔
      (totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
        totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) := by
  constructor
  · rintro ⟨hmax, hmin⟩; exact uc_totalTurn_eq_four_of_winds K a hmax hmin
  · exact uc_winds_of_totalTurn_eq_four K a


theorem uc_turningIsFullRevolution_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hmax : uc_WindsAtMostOnce K a) (hmin : uc_WindsAtLeastOnce K a) :
    TurningIsFullRevolution K a :=
  uc_totalTurn_eq_four_of_winds K a hmax hmin


theorem uc_base_totalTurn_eq_four (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = 4 ∨
      totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = -4 :=
  gbe_singleton_totalTurn_eq_four v a


theorem uc_step_preserves_turn (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowTurn K' e' 0 m' = umEar_windowTurn K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) :=
  gbe_ear_step_preserves_turn K K' e e' m m' n hmatch hbal


theorem uc_turningIsFullRevolution (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_contraction
    (bpc_balancePreservingContraction_of_saturating hsat) K hK hne a


theorem uc_totalTurn_eq_four (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 :=
  uc_turningIsFullRevolution hsat K hK hne a


open Real in


theorem uc_totalTurnAngle_eq_two_pi_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (totalTurnAngle K a.1 (dartOrbitPeriod K a) = 2 * Real.pi ∨
        totalTurnAngle K a.1 (dartOrbitPeriod K a) = -(2 * Real.pi)) ↔
      (totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
        totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [umBase_totalTurnAngle_eq]
  constructor
  · rintro (h | h)
    · left
      have : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) = 4 := by
        have hh : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) * (Real.pi / 2)
            = 4 * (Real.pi / 2) := by rw [h]; ring
        exact mul_right_cancel₀ (by positivity) hh
      exact_mod_cast this
    · right
      have : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) = -4 := by
        have hh : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) * (Real.pi / 2)
            = (-4) * (Real.pi / 2) := by rw [h]; ring
        exact mul_right_cancel₀ (by positivity) hh
      exact_mod_cast this
  · rintro (h | h)
    · left; rw [h]; push_cast; ring
    · right; rw [h]; push_cast; ring

open Real in


theorem uc_totalTurnAngle_eq_two_pi (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnAngle K a.1 (dartOrbitPeriod K a) = 2 * Real.pi ∨
      totalTurnAngle K a.1 (dartOrbitPeriod K a) = -(2 * Real.pi) :=
  (uc_totalTurnAngle_eq_two_pi_iff K a).mpr (uc_totalTurn_eq_four hsat K hK hne a)


theorem uc_unitCell_totalTurn_eq_four :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨
      totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 :=
  unitCell_turningIsFullRevolution

open Real in


theorem uc_unitCell_totalTurnAngle_eq_two_pi :
    totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 2 * Real.pi ∨
      totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -(2 * Real.pi) :=
  Or.inr umBase_square_turning_period


theorem uc_unitCell_winds :
    uc_WindsAtMostOnce unitCell ucBase ∧ uc_WindsAtLeastOnce unitCell ucBase :=
  uc_winds_of_totalTurn_eq_four unitCell ucBase uc_unitCell_totalTurn_eq_four


theorem uc_domino_totalTurn_eq_four :
    totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨
      totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 :=
  domino_turningIsFullRevolution

open Real in


theorem uc_domino_totalTurnAngle_eq_two_pi :
    totalTurnAngle domino dmBase.1 (dartOrbitPeriod domino dmBase) = 2 * Real.pi ∨
      totalTurnAngle domino dmBase.1 (dartOrbitPeriod domino dmBase) = -(2 * Real.pi) := by
  right
  rw [show (dmBase).1 = dmD0 from rfl, domino_orbitPeriod_eq_six]
  exact umBase_domino_turning


theorem uc_domino_winds :
    uc_WindsAtMostOnce domino dmBase ∧ uc_WindsAtLeastOnce domino dmBase :=
  uc_winds_of_totalTurn_eq_four domino dmBase uc_domino_totalTurn_eq_four


theorem uc_domino_saturating_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase :=
  bpc_domino_balanceSaturatingContraction_witness


theorem uc_winds_iff_turningIsFullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a) ↔ TurningIsFullRevolution K a := by
  rw [uc_winds_iff]; rfl


theorem uc_rot90Fun_add (x y : Site 2) : rot90Fun (x + y) = rot90Fun x + rot90Fun y := by
  funext i
  fin_cases i
  · show -(x + y) 1 = -x 1 + -y 1
    rw [Pi.add_apply]; ring
  · show (x + y) 0 = x 0 + y 0
    rw [Pi.add_apply]


end Lattice
end StatMech
