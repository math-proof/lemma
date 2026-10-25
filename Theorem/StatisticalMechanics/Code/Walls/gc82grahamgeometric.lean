/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc82grahamgeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc81grahamthreereplica.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc17core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc10allconnforcing
import Def.StatisticalMechanics.Code.Walls.gc82grahamgeometric.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc82_ThreeGapNonpos_iff_gc15 (β h : ℝ) (o x y : V) :
    gc82_ThreeGapNonpos G β h o x y ↔ gc15_PerConfigUrsellSign G β h o x y := Iff.rfl


end StatMech.Walls
