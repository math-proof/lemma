/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfkforestcount
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


def bgf3_armEdges {V : Type*} {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ) : Set (Sym2 V) :=
  {e | ∃ (α : Arm) (k : ℕ), k < len α ∧ e = s(ray α k, ray α (k + 1))}


def bgf3_G {V : Type*} {Arm : Type*} (ray : Arm → ℕ → V) (len : Arm → ℕ) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (bgf3_armEdges ray len)


end StatMech.Walls
