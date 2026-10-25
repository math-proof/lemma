/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part7
open scoped BigOperators


set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


theorem numClustersWired_eq_card (ω : Sym2 V → Bool) :
    numClustersWired G bdry ω
      = Fintype.card (wiredGraph G bdry ω).ConnectedComponent := by
  rw [numClustersWired, Nat.card_eq_fintype_card]


theorem numClustersWired_le_numClustersFree (ω : Sym2 V → Bool) :
    numClustersWired G bdry ω ≤ numClustersFree G ω :=
  SimpleGraph.ConnectedComponent.card_le_card_of_le (openGraph_le_wiredGraph G bdry ω)


end Lattice
end StatMech
