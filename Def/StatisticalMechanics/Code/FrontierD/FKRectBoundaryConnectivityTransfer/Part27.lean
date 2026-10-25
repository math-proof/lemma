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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part24
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectCoordinateLayerEdge {W n : Nat} (hW : 0 < W)
    (i : Fin n) (evenRow : Bool) (a : Bool × Fin W) :
    Sym2 (Fin W × Fin (n + 1)) :=
  s((fkRectCoordinateLayerEdgeEndpoints hW i evenRow a).1,
    (fkRectCoordinateLayerEdgeEndpoints hW i evenRow a).2)

end
end StatMech.FrontierD
