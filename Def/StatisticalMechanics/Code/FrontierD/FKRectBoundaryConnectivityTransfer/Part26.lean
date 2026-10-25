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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part23
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectCoordinateLayerEdgeEndpoints {W n : Nat} (hW : 0 < W)
    (i : Fin n) (evenRow : Bool) (a : Bool × Fin W) :
    (Fin W × Fin (n + 1)) × (Fin W × Fin (n + 1)) :=
  if a.1 then
    ((a.2, i.castSucc), (a.2, i.succ))
  else if evenRow then
    ((SixVertexArrows.cyclicPred hW a.2, i.castSucc), (a.2, i.succ))
  else
    ((a.2, i.castSucc),
      (SixVertexArrows.cyclicPred hW a.2, i.succ))

end
end StatMech.FrontierD
