/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_bracketsign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.EnsembleGHS
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc5_bracket (μ P : ℝ) : ℝ := -2 * μ * P


end StatMech.Walls
