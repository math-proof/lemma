/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc25resummation.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc24deltabridge.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc27polyineq
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


def gc27_TwoSourceGapFamily (a b c r q p t : ℝ) : Prop :=
  
  (a * a ≤ 1 ∧ b * b ≤ 1 ∧ c * c ≤ 1 ∧ r * r ≤ 1 ∧ q * q ≤ 1 ∧ p * p ≤ 1 ∧ t * t ≤ 1)
  
  ∧ (a * b ≤ r ∧ a * c ≤ q ∧ b * c ≤ p)
  
  ∧ (a * p ≤ t ∧ b * q ≤ t ∧ c * r ≤ t)
  
  ∧ (a * q ≤ c ∧ a * r ≤ b ∧ b * p ≤ c ∧ b * r ≤ a ∧ c * p ≤ b ∧ c * q ≤ a)
  
  ∧ (a * t ≤ p ∧ b * t ≤ q ∧ c * t ≤ r)
  
  ∧ (p * q ≤ r ∧ p * r ≤ q ∧ q * r ≤ p)
  
  ∧ (p * t ≤ a ∧ q * t ≤ b ∧ r * t ≤ c)


end StatMech.Walls
