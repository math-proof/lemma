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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part18
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundaryLayerTransfer {W : Nat} (hW : 0 < W)
    (q : Real) (evenRow : Bool) :
    Matrix (FKRectBoundaryState W) (FKRectBoundaryState W) Real := by
  classical
  exact fun source target =>
    ∑ eta : Bool × Fin W -> Bool,
      if fkRectBoundaryLayerOutput hW evenRow source eta = target then
        fkRectBoundaryLayerWeight hW q evenRow source eta
      else 0


def fkRectBoundaryTwoLayerTransfer {W : Nat} (hW : 0 < W)
    (q : Real) :
    Matrix (FKRectBoundaryState W) (FKRectBoundaryState W) Real :=
  fkRectBoundaryLayerTransfer hW q false *
    fkRectBoundaryLayerTransfer hW q true

end
end StatMech.FrontierD
