/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc71spanningtree.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Def.StatisticalMechanics.Code.Walls.bc72quotient
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


@[simp] theorem bc72_quotGraph_adj {V B : Type*} (G : SimpleGraph V) (f : V → B) (u v : B) :
    (bc72_quotGraph G f).Adj u v ↔ u ≠ v ∧ ∃ a b, f a = u ∧ f b = v ∧ G.Adj a b := Iff.rfl


end StatMech.Walls
