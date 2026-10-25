/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc8core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
import Def.StatisticalMechanics.Code.Walls.rc17arbitrary.Part3
open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc17_rbiB_not_increasing : ¬ IsIncreasing rbi_B := by
  rw [IsIncreasing, IsUpperSet]; intro h
  have hle : rc17_fcfg false false ≤ rc17_fcfg true false := by
    intro i; fin_cases i <;> simp [rc17_fcfg]
  have hmem : rc17_fcfg false false ∈ rbi_B := by simp [rbi_B, rc17_fcfg]
  have := h hle hmem
  simp [rbi_B, rc17_fcfg] at this

open Classical in


theorem rc17_rbiB_not_decreasing : ¬ IsDecreasing rbi_B := by
  rw [IsDecreasing, IsLowerSet]; intro h
  have hle : rc17_fcfg true false ≤ rc17_fcfg true true := by
    intro i; fin_cases i <;> simp [rc17_fcfg]
  have hmem : rc17_fcfg true true ∈ rbi_B := by simp [rbi_B, rc17_fcfg]
  have := h hle hmem
  simp [rbi_B, rc17_fcfg] at this


theorem rc17_nonMonotone_rbi :
    ((¬ IsIncreasing rbi_A ∧ ¬ IsDecreasing rbi_A) ∨ (¬ IsIncreasing rbi_B ∧ ¬ IsDecreasing rbi_B))
      ∧ rc5_deficit rbi_A rbi_B ≤ 0 :=
  ⟨Or.inr ⟨rc17_rbiB_not_increasing, rc17_rbiB_not_decreasing⟩, rc7_deficit_rbi⟩


end StatMech.Walls
