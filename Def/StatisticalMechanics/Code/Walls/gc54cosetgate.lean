/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc54cosetgate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc53count.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc54cosetgate
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

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


def gc54_GateShiftInjection (ends : ι → Sym2 W) (K P₀ : Finset ι) (o x g : W) : Prop :=
    ∃ C, C ⊆ univ \ K ∧ sources ends C = (∅ : Finset W)
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g, connK ends (K ∪ ((L ∆ C) ∆ P₀)) x g


end Abstract
end StatMech.Walls
