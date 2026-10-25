/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.PressureDiff
import Theorem.StatisticalMechanics.Code.FK.DlrSandwich
import Theorem.StatisticalMechanics.Code.FK.Uniqueness
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.FK.FKUniquenessFull
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace


section InfiniteVolume

open StatMech.Lattice


theorem isIncreasing_fkEdgeOpenEvent {E : Type*} (e : E) :
    IsIncreasing (fkEdgeOpenEvent e) := by
  intro x y hxy hx
  simp only [fkEdgeOpenEvent, mem_setOf_eq] at hx ⊢
  have hle := hxy e
  rw [hx] at hle
  exact le_antisymm (by simp) hle


end InfiniteVolume
end FK
end StatMech
