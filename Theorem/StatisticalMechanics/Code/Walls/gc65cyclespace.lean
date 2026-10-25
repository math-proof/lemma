/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc61parallelg.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc64twocommodity
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


theorem gc65_degK_add_sdiff (ends : ι → Sym2 W) (D : Finset ι) (g : W) :
    degK ends (univ : Finset ι) g = degK ends D g + degK ends ((univ : Finset ι) \ D) g := by
  unfold degK
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (Finset.disjoint_sdiff))]
  congr 1
  ext i
  constructor
  · intro hi
    rw [Finset.mem_filter] at hi
    obtain ⟨-, hgi⟩ := hi
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hiD : i ∈ D
    · exact Or.inl ⟨hiD, hgi⟩
    · exact Or.inr ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hiD⟩, hgi⟩
  · intro hi
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hi
    rw [Finset.mem_filter]
    rcases hi with ⟨-, hgi⟩ | ⟨-, hgi⟩ <;> exact ⟨Finset.mem_univ _, hgi⟩


theorem gc65_ygConnector_gDeg_odd (ends : ι → Sym2 W) {D : Finset ι} {y g : W}
    (hDsrc : sources ends D = ({y, g} : Finset W)) : Odd (degK ends D g) := by
  rw [← mem_sources, hDsrc]; simp


theorem gc65_gDegGe3_room (ends : ι → Sym2 W) {D : Finset ι} {g : W}
    (hge3 : 3 ≤ degK ends (univ : Finset ι) g) (hD1 : degK ends D g = 1) :
    2 ≤ degK ends ((univ : Finset ι) \ D) g := by
  have hadd := gc65_degK_add_sdiff ends D g
  omega


theorem gc65_room_of_gDeg1_ygConnector (ends : ι → Sym2 W) {D : Finset ι} {y g : W}
    (hge3 : 3 ≤ degK ends (univ : Finset ι) g)
    (hDsrc : sources ends D = ({y, g} : Finset W)) (hD1 : degK ends D g = 1) :
    2 ≤ degK ends ((univ : Finset ι) \ D) g :=
  gc65_gDegGe3_room ends hge3 hD1


end Abstract
end StatMech.Walls
