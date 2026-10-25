/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc48pairinject.Part2
import Def.StatisticalMechanics.Code.Walls.gc49nullity2
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


theorem gc49_doubled_le_of_innerDom (ends : ι → Sym2 W) (o x y g : W)
    (h : gc49_InnerDom ends o x y g) :
    #(gc48_LHSdoubled ends o x y g) ≤ #(gc48_RHSdoubled ends o x y g) := by
  rw [gc49_LHSdoubled_card_eq_sum, gc49_RHSdoubled_card_eq_sum]
  exact h


theorem gc49_EMassResidue_of_innerDom (ends : ι → Sym2 W) (o x y g : W)
    (h : gc49_InnerDom ends o x y g) :
    gc42_EMassResidue ends o x y g :=
  (gc48_EMassResidue_iff_doubled_le ends o x y g).mpr (gc49_doubled_le_of_innerDom ends o x y g h)


theorem gc49_innerDom_iff_EMassResidue (ends : ι → Sym2 W) (o x y g : W) :
    gc49_InnerDom ends o x y g ↔ gc42_EMassResidue ends o x y g := by
  rw [gc48_EMassResidue_iff_doubled_le, gc49_LHSdoubled_card_eq_sum, gc49_RHSdoubled_card_eq_sum]
  rfl


theorem gc49_countIneq_of_innerDom (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : gc49_InnerDom ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc42_countIneq_of_EMass ends hnd hox hoy hog hxy hxg hyg huniv
    (gc49_EMassResidue_of_innerDom ends o x y g h)

end Abstract
end StatMech.Walls
