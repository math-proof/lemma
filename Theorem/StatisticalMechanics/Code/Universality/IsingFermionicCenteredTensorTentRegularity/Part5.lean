/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Mathlib.Topology.UnitInterval
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part4


namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

theorem isingCenteredRadialGridCoordinate_cellPoint
    (mesh : Real) (hmesh : mesh ≠ 0) (n i j : Nat) (x y : Real) :
    isingCenteredRadialGridCoordinate mesh n
        (isingCenteredRadialGridCellPoint mesh n i j x y) =
      ((i : Real) + x, (j : Real) + y) := by
  unfold isingCenteredRadialGridCoordinate isingCenteredRadialGridCellPoint
  rw [sub_add_cancel]
  exact isingRadialGridCoordinate_cellPoint mesh hmesh i j x y

theorem isingCenteredRadialGridCellPoint_coordinate
    (mesh : Real) (hmesh : mesh ≠ 0) (n i j : Nat) (z : Complex) :
    isingCenteredRadialGridCellPoint mesh n i j
        ((isingCenteredRadialGridCoordinate mesh n z).1 - i)
        ((isingCenteredRadialGridCoordinate mesh n z).2 - j) = z := by
  unfold isingCenteredRadialGridCoordinate isingCenteredRadialGridCellPoint
    isingRadialGridCoordinate isingRadialGridCellPoint
  apply Complex.ext <;> simp <;> field_simp <;> ring


theorem exists_twoByTwo_cell_of_centeredCoordinate
    (n : Nat) (u : Real) (hlo : 1 < u)
    (hhi : u < (2 * n : Nat) - 2) :
    ∃ i : Nat, i + 2 < 2 * n ∧ (i : Real) < u ∧ u < (i : Real) + 2 := by
  let c : Nat := ⌈u⌉₊
  have hu0 : 0 ≤ u := by linarith
  have hcpos : 0 < c := Nat.ceil_pos.mpr (by linarith)
  have hone : 1 ≤ c := hcpos
  have hn : 2 ≤ n := by
    by_contra hn
    have hn' : n ≤ 1 := by omega
    interval_cases n <;> norm_num at hhi <;> linarith
  have htwo : 2 ≤ 2 * n := by omega
  have hcle : c ≤ 2 * n - 2 := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_sub htwo]
    norm_num [Nat.cast_mul]
    simpa [Nat.cast_mul] using hhi.le
  refine ⟨c - 1, ?_, ?_, ?_⟩
  · omega
  · have hc_lt : (c : Real) < u + 1 := Nat.ceil_lt_add_one hu0
    rw [Nat.cast_sub hone]
    norm_num
    linarith
  · have hu_le : u ≤ (c : Real) := Nat.le_ceil u
    rw [Nat.cast_sub hone]
    norm_num
    linarith


end
end StatMech.Universality
