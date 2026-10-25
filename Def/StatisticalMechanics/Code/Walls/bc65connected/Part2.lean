/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc64coarseembed.Part5
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Theorem.StatisticalMechanics.Code.Walls.bc65connected
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc65_cat2E (a b : Fin 6) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨      
  (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨      
  (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
  (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) ∨      
  (a = 1 ∧ b = 5) ∨ (a = 5 ∧ b = 1)

end StatMech.Walls
