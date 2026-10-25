/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc51minpath.Part4
import Def.StatisticalMechanics.Code.Walls.gc52switchinj
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

open StatMech.Sharpness.RandomCurrent (sources connK sources_symmDiff)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc52_perKCount_iff_perKDom (ends : ι → Sym2 W) {o x y g : W} :
    gc52_PerKCount ends o x y g ↔ gc50_PerKDom ends o x y g := Iff.rfl


theorem gc52_switchInjective_of_perKCount (ends : ι → Sym2 W) {o x y g : W}
    (h : gc52_PerKCount ends o x y g) :
    ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      gc51_SwitchInjective ends K o x y g := by
  intro K hK
  exact (gc52_switchInjective_iff_gc50_count ends K).2 (h K hK)


theorem gc52_countIneq_of_perKCount (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : gc52_PerKCount ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc51_countIneq_of_switchInjective ends hnd hox hoy hog hxy hxg hyg huniv
    (gc52_switchInjective_of_perKCount ends h)

end Abstract

open Classical


theorem gc52_witness_count_K13 :
    #(gc51_LblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 3)
      ≤ #(gc51_RblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3) := by
  rw [gc51_witness_LblockSet_K13, gc51_witness_RblockSet_K13, Finset.card_singleton,
    Finset.card_singleton]


theorem gc52_witness_count_K23 :
    #(gc51_LblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 3)
      ≤ #(gc51_RblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3) := by
  rw [gc51_witness_LblockSet_K23, gc51_witness_RblockSet_K23, Finset.card_singleton,
    Finset.card_singleton]


theorem gc52_witness_switchInjective_K13_via_count :
    gc51_SwitchInjective gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 :=
  gc52_switchInjective_of_card_le gc49_witnessEnds _ gc52_witness_count_K13


theorem gc52_witness_switchInjective_K23_via_count :
    gc51_SwitchInjective gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 :=
  gc52_switchInjective_of_card_le gc49_witnessEnds _ gc52_witness_count_K23


theorem gc52_witness_perKDom : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rw [← gc51_LblockSet_card, ← gc51_RblockSet_card]
  rcases hK with rfl | rfl
  · exact gc52_witness_count_K13
  · exact gc52_witness_count_K23

end StatMech.Walls
