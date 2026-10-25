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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part29
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundarySeamEdgeEndpoints_ne {W : Nat} (hW : 0 < W)
    (a : Bool × Fin W) :
    (fkRectBoundarySeamEdgeEndpoints hW a).1 ≠
      (fkRectBoundarySeamEdgeEndpoints hW a).2 := by
  cases a with
  | mk dir x => cases dir <;> simp [fkRectBoundarySeamEdgeEndpoints]


end
end StatMech.FrontierD
