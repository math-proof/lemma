/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part8
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

theorem pfdOuterLeaf_numClusters_eq (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) :
    Nat.card (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).ConnectedComponent =
      Nat.card (pfdClosedDual P K).ConnectedComponent := by
  exact Nat.card_congr (pfdOuterLeafComponentEquiv P K)


theorem pfdDualWeight_eq_outerLeaf (P : PlanarZ2Subgraph)
    (p q : Real) (K : SimpleGraph P.V) :
    pfdDualWeight P p q K =
      edgeProductCount p P.G.edgeFinset.card
          (P.G.edgeFinset.card - K.edgeSet.ncard) *
        q ^ Nat.card (pfdOuterLeafWiredGraph P
          (pfdOuterLeafClosedEdges P K)).ConnectedComponent := by
  unfold pfdDualWeight
  rw [pfdOuterLeaf_numClusters_eq]


theorem fkSquareBox_pfdDualWeight_eq_outerLeaf (n : Nat)
    (p q : Real) (K : SimpleGraph (FK.boxVerts 2 n)) :
    pfdDualWeight (fkSquareBoxPlanar n) p q K =
      edgeProductCount p (FK.boxGraph 2 n).edgeFinset.card
          ((FK.boxGraph 2 n).edgeFinset.card - K.edgeSet.ncard) *
        q ^ Nat.card (pfdOuterLeafWiredGraph (fkSquareBoxPlanar n)
          (pfdOuterLeafClosedEdges (fkSquareBoxPlanar n) K)).ConnectedComponent := by
  exact pfdDualWeight_eq_outerLeaf (fkSquareBoxPlanar n) p q K

end
end StatMech.FrontierD
