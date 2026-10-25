/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9assembledDnonneg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc8core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc8crossingallconn
import Def.StatisticalMechanics.Code.Walls.gc9assembledDnonneg.Part2
open Finset BigOperators SimpleGraph
open scoped Sym2 symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]


theorem gc9_assembledD_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (o g : V) (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m) :
    0 ≤ gc9_assembledD ends F J o g :=
  gc9_assembled_D_nonneg J (gc9_pivotalMass ends F o g) hJ
    (fun x y => gc9_concrete_delta_nonneg ends F hF o g x y)


end StatMech.Walls
