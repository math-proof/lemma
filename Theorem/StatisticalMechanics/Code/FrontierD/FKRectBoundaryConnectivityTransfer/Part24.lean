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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part26
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectCoordinateLayerEdgeEndpoints_last
    {W : Nat} (hW : 0 < W) (n : Nat) (evenRow : Bool)
    (a : Bool × Fin W) :
    Prod.map (fkRectStripVertexEquiv W (n + 1))
        (fkRectStripVertexEquiv W (n + 1))
        (Prod.map (fkRectStripLayerEmbed n) (fkRectStripLayerEmbed n)
          (fkRectLayerEdgeEndpoints hW evenRow a)) =
      fkRectCoordinateLayerEdgeEndpoints hW (Fin.last n) evenRow a := by
  rcases a with ⟨dir, x⟩
  cases dir <;> cases evenRow <;>
    simp [fkRectLayerEdgeEndpoints, fkRectCoordinateLayerEdgeEndpoints,
      fkRectStripLayerEmbed, fkRectLayerInitialRole,
      fkRectLayerOldRole, fkRectLayerNewRole]

end
end StatMech.FrontierD
