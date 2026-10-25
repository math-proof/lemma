/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc46redistribute.Part2
import Def.StatisticalMechanics.Code.Walls.gc47aggregate.Part2
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

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc47_EMassResidue_of_pairInjection (ends : ι → Sym2 W) (o x y g : W)
    (h : gc47_PairInjection ends o x y g) :
    gc42_EMassResidue ends o x y g := by
  obtain ⟨Φ, hmap, hinj⟩ := h
  rw [gc47_EMassResidue_iff_pairCount_le]
  exact Finset.card_le_card_of_injOn Φ hmap hinj


theorem gc47_countIneq_of_pairInjection (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : gc47_PairInjection ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc42_countIneq_of_EMass ends hnd hox hoy hog hxy hxg hyg huniv
    (gc47_EMassResidue_of_pairInjection ends o x y g h)

end Abstract


theorem gc47_defect_LHSpairs_card :
    #(gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) = 7 := by
  rw [gc47_LHSpairs, gc46_defect_Lset]; decide


theorem gc47_defect_RHSpairs_card :
    #(gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) = 7 := by
  rw [gc47_RHSpairs, gc46_defect_Rset]; decide


end StatMech.Walls
