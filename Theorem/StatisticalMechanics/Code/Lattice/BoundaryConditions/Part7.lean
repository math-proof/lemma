/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part6
open scoped BigOperators


set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


@[simp]
theorem wiredGraph_adj (ω : Sym2 V → Bool) (x y : V) :
    (wiredGraph G bdry ω).Adj x y ↔
      (G.Adj x y ∧ ω s(x, y) = true) ∨ (x ≠ y ∧ bdry x ∧ bdry y) := by
  rw [wiredGraph, SimpleGraph.sup_adj, openGraph_adj, boundaryCliqueGraph_adj]

end Lattice
end StatMech
