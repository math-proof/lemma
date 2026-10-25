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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part7
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundaryConnectivityLayerOutput
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryConnectivityState W)
    (eta : Bool × Fin W -> Bool) : FKRectBoundaryConnectivityState W :=
  ⟨fkRectBoundaryLayerOutput hW evenRow state.1 eta,
    fkRectBoundaryLayerOutput_isConnectivity hW evenRow state.1 eta⟩


def fkRectBoundaryLayerClosedCount {W : Nat} (hW : 0 < W)
    (evenRow : Bool) (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : Nat := by
  classical
  let G := fkRectBoundaryLayerGraph hW evenRow state eta
  exact (Finset.univ.filter fun C : G.ConnectedComponent =>
    ∀ u : Bool × Fin W, G.connectedComponentMk
      (fkRectLayerOutputEmbed u) ≠ C).card


end
end StatMech.FrontierD
