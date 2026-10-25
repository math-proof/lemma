/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gh4eq22.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
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
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Walls.GhcEqGap

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gh5_sources_union_of_disjoint (ends : ι → Sym2 W) {S T : Finset ι} (h : Disjoint S T) :
    sources ends (S ∪ T) = sources ends S ∆ sources ends T := by
  have : S ∪ T = S ∆ T := (Disjoint.symmDiff_eq_sup h).symm
  rw [this, sources_symmDiff]


end StatMech.Walls
