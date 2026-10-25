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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part9
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryLayer_component_count
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (eta : Bool × Fin W -> Bool) :
    Fintype.card
        (fkRectBoundaryLayerGraph hW evenRow state eta).ConnectedComponent =
      fkRectBoundaryLayerClosedCount hW evenRow state eta +
        Fintype.card
          (fkRectBoundaryLayerOutput hW evenRow state eta).ConnectedComponent := by
  simpa [fkRectBoundaryLayerClosedCount,
    fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph] using
      finite_component_count_eq_closed_add_boundary
        (fkRectBoundaryLayerGraph hW evenRow state eta)
        (fkRectLayerOutputEmbed : Bool × Fin W -> FKRectLayerVertex W)


end
end StatMech.FrontierD
