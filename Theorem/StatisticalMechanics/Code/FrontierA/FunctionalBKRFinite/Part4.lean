/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part4


namespace StatMech.FrontierA

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [DecidableEq E] in
@[simp] theorem mem_disjointCoordinatePairs {pair : Set E × Set E} :
    pair ∈ disjointCoordinatePairs E ↔ Disjoint pair.1 pair.2 := by
  classical
  simp [disjointCoordinatePairs]

omit [DecidableEq E] in

theorem disjointCoordinatePairs_nonempty : (disjointCoordinatePairs E).Nonempty := by
  classical
  exact ⟨(∅, ∅), by simp⟩


end StatMech.FrontierA
