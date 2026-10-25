/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzEar.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzEar
open SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem umEar_windowTurn_self (K : Set (Site 2)) (e : Dart) (a : ℕ) :
    umEar_windowTurn K e a a = 0 := by
  unfold umEar_windowTurn; rw [Finset.Ico_self, Finset.sum_empty]


theorem umEar_windowTurn_add (K : Set (Site 2)) (e : Dart) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    umEar_windowTurn K e a c = umEar_windowTurn K e a b + umEar_windowTurn K e b c := by
  unfold umEar_windowTurn
  rw [← Finset.sum_Ico_consecutive _ hab hbc]


theorem umEar_totalTurnZ_eq_window (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    totalTurnZ K e p = umEar_windowTurn K e 0 p := by
  unfold totalTurnZ umEar_windowTurn
  rw [Finset.range_eq_Ico]


theorem umEar_totalTurnZ_split (K : Set (Site 2)) (e : Dart) (m p : ℕ) (hm : m ≤ p) :
    totalTurnZ K e p = umEar_windowTurn K e 0 m + umEar_windowTurn K e m p := by
  rw [umEar_totalTurnZ_eq_window]
  exact umEar_windowTurn_add K e 0 m p (Nat.zero_le m) hm


theorem umEar_windowTurn_eq_range (K : Set (Site 2)) (e : Dart) (a n : ℕ) :
    umEar_windowTurn K e a (a + n) =
      ∑ i ∈ Finset.range n, turnZ K ((dartNext K)^[a + i] e) := by
  unfold umEar_windowTurn
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr (by rw [Nat.add_sub_cancel_left])
  intro i _
  rw [Nat.add_comm a i]


theorem umEar_tail_turn_eq (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    umEar_windowTurn K e m (m + n) = umEar_windowTurn K' e' m' (m' + n) := by
  rw [umEar_windowTurn_eq_range, umEar_windowTurn_eq_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  exact hmatch i hi


theorem umEar_contraction_turning_change (K K' : Set (Site 2)) (e e' : Dart)
    (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) +
      (umEar_windowTurn K' e' 0 m' - umEar_windowTurn K e 0 m) := by
  have htail := umEar_tail_turn_eq K K' e e' m m' n hmatch
  rw [umEar_totalTurnZ_split K e m (m + n) (Nat.le_add_right m n),
      umEar_totalTurnZ_split K' e' m' (m' + n) (Nat.le_add_right m' n),
      htail]
  ring


theorem umEar_contraction_preserves_turning (K K' : Set (Site 2)) (e e' : Dart)
    (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowTurn K' e' 0 m' = umEar_windowTurn K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
  rw [umEar_contraction_turning_change K K' e e' m m' n hmatch, hbal]
  ring


end Lattice
end StatMech
