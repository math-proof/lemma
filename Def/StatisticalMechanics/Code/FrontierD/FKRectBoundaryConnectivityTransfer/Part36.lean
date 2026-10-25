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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part33
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundaryListCoefficientSum {W : Nat} (hW : 0 < W)
    (q : Real) : FKRectBoundaryState W -> List Bool -> Real
  | state, [] => fkRectBoundarySeamFunctional hW q state
  | state, evenRow :: rows =>
      ∑ eta : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q evenRow state eta *
          fkRectBoundaryListCoefficientSum hW q
            (fkRectBoundaryLayerOutput hW evenRow state eta) rows

end
end StatMech.FrontierD
