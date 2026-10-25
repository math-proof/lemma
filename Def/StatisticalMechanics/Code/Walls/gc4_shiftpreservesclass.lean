/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc2_shiftbij
import Theorem.StatisticalMechanics.Code.Walls.gc3_twosourceswitch
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent

open StatMech.Ising

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


def gc4_exactlyOneConn (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) : Prop :=
  ¬ aie_allConn ends m o x y ∧ ¬ aie_noneConn ends m o x y


end StatMech.Walls
