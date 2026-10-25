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
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzEar.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem umEar_windowTurn_eq_balance (K : Set (Site 2)) (e : Dart) (a b : ℕ) :
    umEar_windowTurn K e a b = umEar_windowRight K e a b - umEar_windowLeft K e a b := by
  classical
  unfold umEar_windowTurn umEar_windowRight umEar_windowLeft
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases turnZ_mem K ((dartNext K)^[i] e) with h | h | h <;> rw [h] <;> norm_num


theorem umEar_contraction_preserves_turning_balance (K K' : Set (Site 2)) (e e' : Dart)
    (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowRight K' e' 0 m' - umEar_windowLeft K' e' 0 m' =
            umEar_windowRight K e 0 m - umEar_windowLeft K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
  apply umEar_contraction_preserves_turning K K' e e' m m' n hmatch
  rw [umEar_windowTurn_eq_balance K' e' 0 m', umEar_windowTurn_eq_balance K e 0 m, hbal]


theorem umEar_extremeCell_ear_first_turn (K : Set (Site 2)) (c : Site 2)
    (hc : IsExtremeCell K c) :
    turnZ K ((dartNext K)^[0] (leftDart c)) = -1 := by
  rw [Function.iterate_zero_apply]
  exact extremeCell_turnZ K c hc


theorem umEar_extremeCell_one_le_windowLeft (K : Set (Site 2)) (c : Site 2)
    (hc : IsExtremeCell K c) (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ umEar_windowLeft K (leftDart c) 0 m := by
  classical
  unfold umEar_windowLeft
  have hmem : 0 ∈ (Finset.Ico 0 m).filter
      (fun i => turnZ K ((dartNext K)^[i] (leftDart c)) = -1) := by
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Nat.zero_le 0, hm⟩, umEar_extremeCell_ear_first_turn K c hc⟩
  have : 1 ≤ ((Finset.Ico 0 m).filter
      (fun i => turnZ K ((dartNext K)^[i] (leftDart c)) = -1)).card :=
    Finset.card_pos.mpr ⟨0, hmem⟩
  exact_mod_cast this


theorem umEar_domino_contracts_to_unitCell :
    totalTurnZ domino dmD0 6 = totalTurnZ unitCell ucDart0 4 := by
  rw [domino_totalTurnZ_six, unitCell_totalTurnZ_four]


theorem umEar_domino_unitCell_totalTurnZ :
    totalTurnZ domino dmD0 6 = -4 ∧ totalTurnZ unitCell ucDart0 4 = -4 :=
  ⟨domino_totalTurnZ_six, unitCell_totalTurnZ_four⟩

end Lattice
end StatMech
