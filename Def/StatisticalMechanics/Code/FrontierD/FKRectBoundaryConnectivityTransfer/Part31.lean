/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part28
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectStripSeamGraph {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (eta : Bool × Fin W -> Bool) : SimpleGraph (FKRectStripVertex W n) :=
  finiteBoundaryEdgeRun (fkRectStripBoundary n)
    (fkRectStripGraph hW n layers) (fkRectBoundaryOpenSeamEdges hW eta)


def fkRectCoordinateSeamEdge {W n : Nat} (hW : 0 < W)
    (a : Bool × Fin W) : Sym2 (Fin W × Fin (n + 1)) :=
  if a.1 then
    s((a.2, Fin.last n), (a.2, 0))
  else
    s((SixVertexArrows.cyclicPred hW a.2, Fin.last n), (a.2, 0))

end
end StatMech.FrontierD
