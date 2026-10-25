/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc58cyclespace
import Theorem.StatisticalMechanics.Code.Walls.gc59residual
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
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


def gc59_Peelable (ends : ι → Sym2 W) : Finset ι → List ι → Prop
  | _, [] => True
  | G, (i :: rest) =>
      i ∈ G ∧ (∃ p q : W, ends i = s(p, q) ∧ connK ends (G \ {i}) p q)
        ∧ gc59_Peelable ends (G \ {i}) rest


def gc59_removeList : Finset ι → List ι → Finset ι
  | G, [] => G
  | G, (i :: rest) => gc59_removeList (G \ {i}) rest


end Abstract
end StatMech.Walls
