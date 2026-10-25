/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Instance.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part6
open scoped BigOperators


set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


theorem openGraph_le_wiredGraph (ω : Sym2 V → Bool) :
    openGraph G ω ≤ wiredGraph G bdry ω := le_sup_left


theorem wiredGraph_adj_of_bdry {ω : Sym2 V → Bool} {x y : V}
    (hne : x ≠ y) (hx : bdry x) (hy : bdry y) :
    (wiredGraph G bdry ω).Adj x y := by
  rw [wiredGraph_adj]
  exact Or.inr ⟨hne, hx, hy⟩


end Lattice
end StatMech
