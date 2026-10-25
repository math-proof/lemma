/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part6
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

@[simp] theorem pfdOuterLeafWiredGraph_adj (P : PlanarZ2Subgraph)
    (F : Set (kwg_Edge P)) (x y : pfdOuterLeafVertex P) :
    (pfdOuterLeafWiredGraph P F).Adj x y ↔
      (x ≠ y ∧ ∃ e, e ∈ F ∧ pfdOuterLeafEnds P e = s(x, y)) ∨
      (x ≠ y ∧ pfdOuterLeafBoundary P x ∧ pfdOuterLeafBoundary P y) := by
  rw [pfdOuterLeafWiredGraph, SimpleGraph.sup_adj,
    pfdOuterLeafOpenGraph_adj, boundaryCliqueGraph_adj]


end
end StatMech.FrontierD
