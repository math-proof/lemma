/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.EarContraction
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem cornerBalance_eq_totalTurnZ (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance K a = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  unfold cornerBalance
  rw [totalTurnZ_eq_cornerBalance]


theorem simplePolygonCornerBalance_iff_cornerBalance (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    SimplePolygonCornerBalance K a ↔ (cornerBalance K a = 4 ∨ cornerBalance K a = -4) := by
  unfold SimplePolygonCornerBalance cornerBalance
  rfl


theorem extremeCell_up_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    c + ![0, 1] ∉ K := by
  apply extremeCell_not_mem_of_higher K c _ hc; simp [Pi.add_apply]


theorem extremeCell_left_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    c + ![-1, 0] ∉ K := by
  apply extremeCell_not_mem_of_left K c _ hc <;> simp [Pi.add_apply]


theorem adj_neighbor_cases (v c : Site 2) (hadj : (hypercubicLattice 2).Adj v c) :
    v = c + ![1, 0] ∨ v = c + ![-1, 0] ∨ v = c + ![0, 1] ∨ v = c + ![0, -1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have key : ((v 0 - c 0).natAbs = 1 ∧ (v 1 - c 1).natAbs = 0) ∨
             ((v 0 - c 0).natAbs = 0 ∧ (v 1 - c 1).natAbs = 1) := by omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rcases Int.natAbs_eq_iff.mp h0 with h | h
    · left; funext i; fin_cases i <;> simp [Pi.add_apply] <;> omega
    · right; left; funext i; fin_cases i <;> simp [Pi.add_apply] <;> omega
  · rcases Int.natAbs_eq_iff.mp h1 with h | h
    · right; right; left; funext i; fin_cases i <;> simp [Pi.add_apply] <;> omega
    · right; right; right; funext i; fin_cases i <;> simp [Pi.add_apply] <;> omega


theorem extremeCell_neighbor_right_or_down (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj v c) :
    v = c + ![1, 0] ∨ v = c + ![0, -1] := by
  rcases adj_neighbor_cases v c hadj with h | h | h | h
  · exact Or.inl h
  · exact absurd (h ▸ hv) (extremeCell_left_nmem K c hc)
  · exact absurd (h ▸ hv) (extremeCell_up_nmem K c hc)
  · exact Or.inr h


end Lattice
end StatMech
