/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh4eq22.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Theorem.StatisticalMechanics.Code.Walls.gh3weightedcor3.Part2
import Theorem.StatisticalMechanics.Code.Walls.gh4eq22
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


noncomputable def gh4_compMass (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (A : Finset ι) : ℕ :=
  #((m.powerset ×ˢ m.powerset).filter
      (fun KK => Disjoint KK.1 KK.2 ∧ sources ends KK.1 = V₁ ∧ sources ends KK.2 = V₂
        ∧ gh4_bondCompOf ends KK.1 u = A))


end StatMech.Walls
