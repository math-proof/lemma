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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part5
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectLayerEdgeEndpoints {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (a : Bool × Fin W) : FKRectLayerVertex W × FKRectLayerVertex W :=
  if a.1 then
    ((fkRectLayerOldRole, a.2), (fkRectLayerNewRole, a.2))
  else if evenRow then
    ((fkRectLayerOldRole, SixVertexArrows.cyclicPred hW a.2),
      (fkRectLayerNewRole, a.2))
  else
    ((fkRectLayerOldRole, a.2),
      (fkRectLayerNewRole, SixVertexArrows.cyclicPred hW a.2))

end
end StatMech.FrontierD
