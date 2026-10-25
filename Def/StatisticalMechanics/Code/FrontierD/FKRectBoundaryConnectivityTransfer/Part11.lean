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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part9
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundaryLayerOpenCount {W : Nat}
    (eta : Bool × Fin W -> Bool) : Nat :=
  (Finset.univ.filter fun a => eta a = true).card


def fkRectBoundaryOpenLayerIndices {W : Nat}
    (eta : Bool × Fin W -> Bool) : List (Bool × Fin W) :=
  (Finset.univ.filter fun a => eta a = true).toList


def fkRectBoundaryOpenLayerEdges {W : Nat} (hW : 0 < W)
    (evenRow : Bool) (eta : Bool × Fin W -> Bool) :
    List (FKRectLayerVertex W × FKRectLayerVertex W) :=
  (fkRectBoundaryOpenLayerIndices eta).map
    (fkRectLayerEdgeEndpoints hW evenRow)


end
end StatMech.FrontierD
