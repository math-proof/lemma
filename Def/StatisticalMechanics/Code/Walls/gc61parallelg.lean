/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc60exhaustive.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc61parallelg
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


def gc61_ParallelTwinPresent (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ D i v, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ends i = s(v, g) ∧ v ≠ g
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g,
          connK ends (K ∪ L) x g ∧
          ((D ∩ (K ∪ L) = {i} ∧ i ∈ K ∪ L ∧ connK ends ((K ∪ L) \ {i}) v g)
            ∨ D ∩ (K ∪ L) = ∅)


end Abstract
end StatMech.Walls
