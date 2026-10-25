/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc65cyclespace.Part2
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
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc66_ygConnector_connK (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {D : Finset ι} {y g : W} (hyg : y ≠ g) (hDsrc : sources ends D = ({y, g} : Finset W)) :
    connK ends D y g := by
  apply path_exists ends D (fun i _ => hnd i) y g
  · rw [← mem_sources, hDsrc]; simp
  · intro z hz; rw [← mem_sources, hDsrc] at hz; simpa using hz
  · exact hyg


theorem gc66_strictly_smaller_of_removable (ends : ι → Sym2 W) {D : Finset ι} {y g : W} (hyg : y ≠ g)
    {i₀ : ι} (hi₀ : i₀ ∈ D) (hrem : connK ends (D \ {i₀}) y g) :
    ∃ D', D' ⊆ D ∧ sources ends D' = ({y, g} : Finset W) ∧ #D' < #D := by
  obtain ⟨D', hD'sub, hD'src⟩ := exists_conn_set ends (D \ {i₀}) hrem hyg
  refine ⟨D', hD'sub.trans Finset.sdiff_subset, hD'src, ?_⟩
  have hcard : #(D \ {i₀}) = #D - 1 := by
    rw [show D \ {i₀} = D.erase i₀ from Finset.sdiff_singleton_eq_erase _ _,
      Finset.card_erase_of_mem hi₀]
  calc #D' ≤ #(D \ {i₀}) := Finset.card_le_card hD'sub
    _ = #D - 1 := hcard
    _ < #D := by
        have : 1 ≤ #D := Finset.card_pos.2 ⟨i₀, hi₀⟩
        omega


end Abstract
end StatMech.Walls
