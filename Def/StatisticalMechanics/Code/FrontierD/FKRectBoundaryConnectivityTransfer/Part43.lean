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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part40
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundaryAlternatingCoefficientSum {W : Nat} (hW : 0 < W)
    (q : Real) (state : FKRectBoundaryState W) : Nat -> Real
  | 0 =>
      ∑ oddLayer : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q false state oddLayer *
          fkRectBoundarySeamFunctional hW q
            (fkRectBoundaryLayerOutput hW false state oddLayer)
  | blocks + 1 =>
      ∑ oddLayer : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q false state oddLayer *
          ∑ evenLayer : Bool × Fin W -> Bool,
            fkRectBoundaryLayerWeight hW q true
                (fkRectBoundaryLayerOutput hW false state oddLayer)
                evenLayer *
              fkRectBoundaryAlternatingCoefficientSum hW q
                (fkRectBoundaryLayerOutput hW true
                (fkRectBoundaryLayerOutput hW false state oddLayer)
                  evenLayer) blocks

end
end StatMech.FrontierD
