/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FieldGhostDict

variable {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V] [Fintype V]


def gc8_disconn (ends : ι → Sym2 V) (o g : V) (m : Finset ι) : Prop :=
  ¬ connK ends m o g


def gc8_caseA (ends : ι → Sym2 V) (o x y g : V) (m : Finset ι) : Prop :=
  (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g)


def gc8_caseB (ends : ι → Sym2 V) (o x y g : V) (m : Finset ι) : Prop :=
  (¬ connK ends m o g) ∧ (connK ends m o y ∧ connK ends m x g)


end StatMech.Walls
