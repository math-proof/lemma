/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc42countproof.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc43graham
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


noncomputable def gc43_Lset (ends : ι → Sym2 W) (o x y g : W) : Finset (Finset ι) :=
  (univ : Finset ι).powerset.filter
    (fun M => sources ends M = ({o, x} : Finset W) ∧ connK ends M x g)


noncomputable def gc43_Rset (ends : ι → Sym2 W) (o x y g : W) : Finset (Finset ι) :=
  (univ : Finset ι).powerset.filter
    (fun M => sources ends M = ({o, x, y, g} : Finset W)
      ∧ connK ends M o x ∧ connK ends M o y ∧ connK ends M o g)


end Abstract
end StatMech.Walls
