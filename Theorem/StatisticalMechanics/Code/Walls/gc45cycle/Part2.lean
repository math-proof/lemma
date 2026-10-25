/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc44flow.Part2
import Def.StatisticalMechanics.Code.Walls.gc45cycle.Part2
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


theorem gc45_fibreDomReloc_of_count_le (ends : ι → Sym2 W) (o x y g : W)
    (htree : gc45_TreeLHS ends o x y g)
    (φ : Finset ι → Finset ι)
    (hmaps : ∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
    (hcount : ∀ M' ∈ gc43_Rset ends o x y g,
        #((gc43_Lset ends o x y g).filter (fun M => φ M = M')) ≤ gc40_E ends M') :
    gc43_FibreDomReloc ends o x y g := by
  refine ⟨φ, hmaps, ?_⟩
  intro M' hM'
  set fib := (gc43_Lset ends o x y g).filter (fun M => φ M = M') with hfib
  
  have hsum : (∑ M ∈ fib, gc40_E ends M) = #fib := by
    rw [Finset.sum_congr rfl (fun M hM => ?_), Finset.sum_const, smul_eq_mul, mul_one]
    
    rw [hfib, Finset.mem_filter] at hM
    exact htree M hM.1
  rw [hsum]
  exact hcount M' hM'


end Abstract
end StatMech.Walls
