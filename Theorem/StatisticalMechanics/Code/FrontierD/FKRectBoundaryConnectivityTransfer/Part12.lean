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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part13
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryEmptyLayer_boundaryGraph_eq
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (hstate : state.IsConnectivity) :
    finiteBoundaryConnectivityGraph
        (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer)
        fkRectLayerInputEmbed = state := by
  ext u v
  change (u ≠ v ∧
      (fkRectBoundaryLayerGraph hW evenRow state
        fkRectBoundaryEmptyLayer).Reachable
          (fkRectLayerInputEmbed u) (fkRectLayerInputEmbed v)) ↔ state.Adj u v
  rw [fkRectBoundaryEmptyLayer_input_reachable_iff, hstate]


theorem fkRectBoundaryEmptyLayer_component_count
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (hstate : state.IsConnectivity) :
    Fintype.card (fkRectBoundaryLayerGraph hW evenRow state
        fkRectBoundaryEmptyLayer).ConnectedComponent =
      Fintype.card state.ConnectedComponent + W := by
  classical
  let G := fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer
  have hsplit := finite_component_count_eq_closed_add_boundary
    G (fkRectLayerInputEmbed : Bool × Fin W -> FKRectLayerVertex W)
  have hclosed :
      (Finset.univ.filter fun C : G.ConnectedComponent =>
        ∀ u : Bool × Fin W, G.connectedComponentMk
          (fkRectLayerInputEmbed u) ≠ C).card = W := by
    rw [← Fintype.card_subtype]
    simpa [G] using Fintype.card_congr
      (fkRectBoundaryEmptyLayerClosedComponentEquiv hW evenRow state).symm
  rw [hclosed, fkRectBoundaryEmptyLayer_boundaryGraph_eq hW evenRow state hstate]
    at hsplit
  simpa [G, Nat.add_comm] using hsplit


end
end StatMech.FrontierD
