/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc46redistribute.Part2
import Def.StatisticalMechanics.Code.Walls.gc47aggregate
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


theorem gc47_gatedSum_eq_sigma_card (ends : ι → Sym2 W) (s : Finset (Finset ι)) :
    (∑ M ∈ s, gc40_E ends M) = #(s.sigma (fun M => gc45_evenSub ends M)) := by
  rw [Finset.card_sigma]
  exact Finset.sum_congr rfl (fun M _ => gc45_E_eq_card_evenSub ends M)


theorem gc47_LHSpairs_card (ends : ι → Sym2 W) (o x y g : W) :
    (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)),
        (if connK ends M x g then gc40_E ends M else 0))
      = #(gc47_LHSpairs ends o x y g) := by
  rw [gc43_LHS_eq_gatedSum, gc47_LHSpairs, gc47_gatedSum_eq_sigma_card]


theorem gc47_RHSpairs_card (ends : ι → Sym2 W) (o x y g : W) :
    (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)),
        (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0))
      = #(gc47_RHSpairs ends o x y g) := by
  rw [gc43_RHS_eq_gatedSum, gc47_RHSpairs, gc47_gatedSum_eq_sigma_card]


theorem gc47_EMassResidue_iff_pairCount_le (ends : ι → Sym2 W) (o x y g : W) :
    gc42_EMassResidue ends o x y g
      ↔ #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g) := by
  unfold gc42_EMassResidue
  rw [gc47_LHSpairs_card, gc47_RHSpairs_card]


end Abstract
end StatMech.Walls
