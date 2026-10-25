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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part14
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectStripGraph {W : Nat} (hW : 0 < W) :
    (n : Nat) -> (Fin n -> Bool × (Bool × Fin W -> Bool)) ->
      SimpleGraph (FKRectStripVertex W n)
  | 0, _ => ⊥
  | n + 1, layers =>
      finiteBoundaryEdgeRun (fkRectStripLayerEmbed n)
        ((fkRectStripGraph hW n (fun i => layers i.castSucc)).sum ⊥)
        (fkRectBoundaryOpenLayerEdges hW (layers (Fin.last n)).1
          (layers (Fin.last n)).2)


def fkRectStripState {W : Nat} (hW : 0 < W) :
    (n : Nat) -> (Fin n -> Bool × (Bool × Fin W -> Bool)) ->
      FKRectBoundaryState W
  | 0, _ => fkRectBoundaryInitialState W
  | n + 1, layers =>
      fkRectBoundaryLayerOutput hW (layers (Fin.last n)).1
        (fkRectStripState hW n (fun i => layers i.castSucc))
        (layers (Fin.last n)).2


def fkRectStripClosedCount {W : Nat} (hW : 0 < W) :
    (n : Nat) -> (Fin n -> Bool × (Bool × Fin W -> Bool)) -> Nat
  | 0, _ => 0
  | n + 1, layers =>
      fkRectStripClosedCount hW n (fun i => layers i.castSucc) +
        fkRectBoundaryLayerClosedCount hW (layers (Fin.last n)).1
          (fkRectStripState hW n (fun i => layers i.castSucc))
          (layers (Fin.last n)).2

end
end StatMech.FrontierD
