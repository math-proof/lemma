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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part32
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryTransferCoefficient_eq
    (R : FKRectTorus) (q : Real) (omega : R.Configuration) :
    fkRectBoundaryTransferCoefficient R q omega =
      Real.sqrt q ^ fkRectOpenEdgeCount R omega *
        q ^ fkRectBoundaryTransferClusterCount R omega := by
  rw [fkRectBoundaryTransferCoefficient, fkRectBoundaryRunWeight_eq]
  unfold fkRectBoundarySeamWeight fkRectBoundaryTransferClusterCount
  rw [fkRectOpenEdgeCount_eq_run_add_seam, pow_add, pow_add]
  ring


end
end StatMech.FrontierD
