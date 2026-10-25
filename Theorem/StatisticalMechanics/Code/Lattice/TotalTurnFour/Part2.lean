/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchMatching.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Wall1EmbeddingRetry
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Def.StatisticalMechanics.Code.Lattice.TotalTurnFour
open SimpleGraph Function Set Finset


namespace StatMech

namespace Lattice

theorem ttf_totalTurn_eq_four_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hmax : ttf_WindsAtMostOnce K a) (hmin : ttf_WindsAtLeastOnce K a) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
  have hdvd := ttf_four_dvd_totalTurn K a
  unfold ttf_WindsAtMostOnce at hmax
  unfold ttf_WindsAtLeastOnce at hmin
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


theorem ttf_turningIsFullRevolution_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hmax : ttf_WindsAtMostOnce K a) (hmin : ttf_WindsAtLeastOnce K a) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  ttf_totalTurn_eq_four_of_winds K a hmax hmin


theorem ttf_winds_of_totalTurn_eq_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h : totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) :
    ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a := by
  unfold ttf_WindsAtMostOnce ttf_WindsAtLeastOnce
  rcases h with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩


theorem ttf_winds_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    (ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a) ↔
      (totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
        totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) := by
  constructor
  · rintro ⟨hmax, hmin⟩; exact ttf_totalTurn_eq_four_of_winds K a hmax hmin
  · exact ttf_winds_of_totalTurn_eq_four K a


theorem ttf_totalTurn_eq_four_of_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a)
    (h : EulerCharOne (ndt_StarHull K) a) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  turningIsFullRevolution_of_eulerCharOne (ndt_StarHull K) a hp h


theorem ttf_eulerCharOne_iff_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a) :
    EulerCharOne (ndt_StarHull K) a ↔
      (ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a) := by
  rw [eulerCharOne_iff_turningIsFullRevolution (ndt_StarHull K) a hp]
  unfold TurningIsFullRevolution
  rw [ttf_winds_iff]


theorem ttf_totalTurn_eq_four_of_balancePreservingContraction (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hcontr : BalancePreservingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  turningIsFullRevolution_of_contraction hcontr (ndt_StarHull K) hSK hne a


theorem ttf_unitCell_totalTurn_eq_four :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨
      totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 :=
  unitCell_turningIsFullRevolution


theorem ttf_unitCell_winds :
    |totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)| ≤ 4 ∧
      totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) ≠ 0 := by
  rcases ttf_unitCell_totalTurn_eq_four with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩


theorem ttf_domino_totalTurn_eq_four :
    totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨
      totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 :=
  domino_turningIsFullRevolution


end Lattice
end StatMech
