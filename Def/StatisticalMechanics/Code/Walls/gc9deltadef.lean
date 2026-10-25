/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.SwitchingDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewrite
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc8crossingallconn
import Theorem.StatisticalMechanics.Code.Walls.gc8core.Part2
open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FieldGhostDict

variable {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V] [Fintype V]


noncomputable def gc9_delta (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)


noncomputable def gc9_delta_caseA (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)


noncomputable def gc9_delta_caseB (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m)


end StatMech.Walls
