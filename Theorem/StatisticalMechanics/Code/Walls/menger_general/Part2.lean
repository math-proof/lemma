/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Def.StatisticalMechanics.Code.Walls.menger_general.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm adjStep degK compOf
  sources_symmDiff mem_sources path_exists exists_conn_set)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


@[simp] theorem mngg_mem_familyUnion {j : ℕ} {P : Fin j → Finset ι} {x : ι} :
    x ∈ mngg_familyUnion P ↔ ∃ i, x ∈ P i := by
  simp [mngg_familyUnion]


theorem mngg_familyUnion_subset {ends : ι → Sym2 W} {G : Finset ι} {a b : W} {j : ℕ}
    {P : Fin j → Finset ι} (hP : mngg_DisjointFamily ends G a b P) :
    mngg_familyUnion P ⊆ G := by
  intro x hx
  rw [mngg_mem_familyUnion] at hx
  obtain ⟨i, hi⟩ := hx
  exact (hP.1 i).1 hi


end Abstract
end StatMech.Walls
