module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
public import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
public import Theorem.StatisticalMechanics.Code.Walls.gc8Z0pos
public import Theorem.StatisticalMechanics.Code.Walls.gc8core.Part2
open Finset BigOperators SimpleGraph
open Classical
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Znormaliserpos.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def gc9_Z_normaliser (β : ℝ) (J : Sym2 (Option V) → ℝ) : ℝ :=
  (Sharpness.currentSum (withGhost G) β J ∅) ^ 2


end StatMech.Walls
