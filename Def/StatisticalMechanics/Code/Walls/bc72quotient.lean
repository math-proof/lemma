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


def bc72_quotGraph {V B : Type*} (G : SimpleGraph V) (f : V → B) : SimpleGraph B where
  Adj u v := u ≠ v ∧ ∃ a b, f a = u ∧ f b = v ∧ G.Adj a b
  symm := by constructor; rintro u v ⟨hne, a, b, ha, hb, hab⟩; exact ⟨hne.symm, b, a, hb, ha, hab.symm⟩
  loopless := ⟨by rintro u ⟨h, _⟩; exact h rfl⟩

end StatMech.Walls
