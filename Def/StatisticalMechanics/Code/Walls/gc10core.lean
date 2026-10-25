/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc6_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.gc10ensembleprob
open scoped BigOperators symmDiff
open Finset SimpleGraph Set
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Walls.GhcEqGap

open StatMech.Walls.Gc5EqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc10_GhostFourPointSign (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
    eg_ursell4_ghostPlus G β h o x y
      ≤ -2 * (onePt G β h o * onePt G β h x * onePt G β h y)


end StatMech.Walls
