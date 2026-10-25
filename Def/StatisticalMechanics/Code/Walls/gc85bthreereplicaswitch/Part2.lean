/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc83crosspairing.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch
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

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap


variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


def gc85b_threeGapCount (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : ℤ :=
  (gc85b_pcount ends m ∅ ∅ : ℤ)
    - (gc85b_pcount ends m ∅ {o, g} : ℤ)
    - (gc85b_pcount ends m ∅ {o, x} : ℤ)
    - (gc85b_pcount ends m ∅ {o, y} : ℤ)
    + 2 * (gc85b_pcount ends m {o, g} {x, g} : ℤ)


end StatMech.Walls
