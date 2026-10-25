/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc6_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc8crossingallconn
import Theorem.StatisticalMechanics.Code.Walls.gc8innereq15
import Theorem.StatisticalMechanics.Code.Walls.gc8reinnerpair
import Theorem.StatisticalMechanics.Code.Walls.gc8Z0pos
import Theorem.StatisticalMechanics.Code.Walls.gc8munonneg
import Theorem.StatisticalMechanics.Code.Walls.gc8fourmarks
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc8core
open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable {ι : Type*} [DecidableEq ι] [Fintype ι]


def gc8_PivotalSignBridge (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
    ∃ (D Z' : ℝ), (0 ≤ D) ∧ (0 < Z') ∧ eg_ursell3 G β h o x y * Z' = - D


end StatMech.Walls
