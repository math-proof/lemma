/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc42countproof.Part2
import Def.StatisticalMechanics.Code.Walls.gc43graham
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc43_LHS_eq_gatedSum (ends : ι → Sym2 W) (o x y g : W) :
    (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)),
        (if connK ends M x g then gc40_E ends M else 0))
      = ∑ M ∈ gc43_Lset ends o x y g, gc40_E ends M := by
  rw [gc43_Lset, ← Finset.filter_filter,
    Finset.sum_filter (s := (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)))
      (p := fun M => connK ends M x g) (f := fun M => gc40_E ends M)]


theorem gc43_RHS_eq_gatedSum (ends : ι → Sym2 W) (o x y g : W) :
    (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)),
        (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0))
      = ∑ M ∈ gc43_Rset ends o x y g, gc40_E ends M := by
  rw [gc43_Rset, ← Finset.filter_filter,
    Finset.sum_filter (s := (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)))
      (p := fun M => connK ends M o x ∧ connK ends M o y ∧ connK ends M o g) (f := fun M => gc40_E ends M)]


end Abstract
end StatMech.Walls
