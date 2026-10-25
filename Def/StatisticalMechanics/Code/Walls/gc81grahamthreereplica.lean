/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc25resummation.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc37hdom.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc80bookroute
import Theorem.StatisticalMechanics.Code.Walls.FaithfulnessAudit.Part2
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


noncomputable def cs81 (β h : ℝ) (A : Finset (Option V)) : ℝ :=
  currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) A


noncomputable def gc81_natRes_residual (β h : ℝ) (o x y : V) : ℝ :=
  (gc15_Z0 G β h + 2) * gc25_nativeAllConnMass G β h o x y
    - gc15_Z0 G β h * (cs81 G β h {some o, some x} * cs81 G β h {some y, none})
    - gc15_Z0 G β h * (cs81 G β h {some o, some y} * cs81 G β h {some x, none})
    + 2 * (cs81 G β h {some o, none} * cs81 G β h {some x, none} * cs81 G β h {some y, none})


end StatMech.Walls
