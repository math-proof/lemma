/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc56pathremoval.Part3
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

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc57_graph_sdiff (K L D : Finset ι) (hKD : Disjoint K D) :
    (K ∪ L) \ D = K ∪ (L \ D) := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_union]
  rw [Finset.disjoint_left] at hKD
  constructor
  · rintro ⟨hj | hj, hnot⟩
    · exact Or.inl hj
    · exact Or.inr ⟨hj, hnot⟩
  · rintro (hj | ⟨hjL, hjD⟩)
    · exact ⟨Or.inl hj, fun hd => hKD hj hd⟩
    · exact ⟨Or.inr hjL, hjD⟩


theorem gc57_connK_of_disjoint_connector (ends : ι → Sym2 W) {P G D : Finset ι}
    (hPG : P ⊆ G) (hPD : Disjoint P D) {a b : W} (hab : connK ends P a b) :
    connK ends (G \ D) a b := by
  have hsub : P ⊆ G \ D := by
    intro i hi
    rw [Finset.mem_sdiff]
    exact ⟨hPG hi, Finset.disjoint_left.1 hPD hi⟩
  exact gc51_connK_mono ends hsub hab


end Abstract
end StatMech.Walls
