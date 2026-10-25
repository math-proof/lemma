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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part8
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (eta : Bool × Fin W -> Bool) :
    fkRectBoundaryLayerOutput hW evenRow state eta =
      finiteBoundaryConnectivityGraph
        (fkRectBoundaryLayerGraph hW evenRow state eta)
        fkRectLayerOutputEmbed := rfl

theorem finiteBoundaryConnectivityGraph_isConnectivity
    {V B : Type*} (G : SimpleGraph V) (embed : B -> V) :
    ∀ u v,
      (finiteBoundaryConnectivityGraph G embed).Adj u v ↔
        u ≠ v ∧
          (finiteBoundaryConnectivityGraph G embed).Reachable u v := by
  intro u v
  rw [finiteBoundaryConnectivityGraph_reachable_iff]
  rfl

theorem fkRectBoundaryLayerOutput_isConnectivity
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (eta : Bool × Fin W -> Bool) :
    (fkRectBoundaryLayerOutput hW evenRow state eta).IsConnectivity := by
  rw [fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph]
  exact finiteBoundaryConnectivityGraph_isConnectivity _ _


end
end StatMech.FrontierD
