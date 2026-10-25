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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part20
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectOpenEdgeCount_eq_run_add_seam
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenEdgeCount R omega =
      fkRectBoundaryRunOpenCount
          (fkRectConfigurationNonSeamLayers R omega) +
        fkRectBoundaryLayerOpenCount
          (fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R)) := by
  rw [fkRectOpenEdgeCount_eq_sum_layerOpenCount,
    fkRect_sum_rows_eq_seam_add_nonSeam]
  rw [Nat.add_comm]
  congr 1
  rw [fkRectBoundaryRunOpenCount_eq_sum]
  simp [fkRectConfigurationNonSeamLayers, List.map_ofFn,
    List.sum_ofFn]


end
end StatMech.FrontierD
