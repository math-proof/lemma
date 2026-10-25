/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc46redistribute.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc47aggregate
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


def gc47_PairInjection (ends : ι → Sym2 W) (o x y g : W) : Prop :=
  ∃ Φ : (Σ _ : Finset ι, Finset ι) → (Σ _ : Finset ι, Finset ι),
    (∀ p ∈ gc47_LHSpairs ends o x y g, Φ p ∈ gc47_RHSpairs ends o x y g)
      ∧ Set.InjOn Φ (gc47_LHSpairs ends o x y g)


end Abstract
end StatMech.Walls
