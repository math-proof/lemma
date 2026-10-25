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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part42
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem exists_fkRectBoundaryTransferReducedZ_log_div_tendsto
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q) :
    ∃ rate : Real, Tendsto (fun blocks : Nat =>
      Real.log (fkRectBoundaryTransferReducedZ hW q blocks) /
        (blocks : Real)) atTop (nhds rate) := by
  let A := fkRectBoundaryTwoLayerTransfer hW q
  let final := fkRectBoundaryLayerTransfer hW q false *ᵥ
    fkRectBoundarySeamFunctional hW q
  have hA : ∀ source target, 0 ≤ A source target :=
    fkRectBoundaryTwoLayerTransfer_nonneg hW hq
  have hdiag : ∀ state,
      MatrixPositiveReachable A (fkRectBoundaryInitialState W) state →
        0 < A state state := by
    intro state hreach
    exact fkRectBoundaryTwoLayerTransfer_diag_pos_of_isConnectivity hW hq
      state (fkRectBoundaryTwoLayerTransfer_reachable_isConnectivity
        hW hq state hreach)
  have hfinal : ∀ state, 0 < final state :=
    fkRectBoundaryFinalFunctional_pos hW hq
  obtain ⟨rate, hrate⟩ :=
    exists_matrixCoefficient_log_div_tendsto_of_reachable_diag
      A hA (fkRectBoundaryInitialState W) hdiag final hfinal
  refine ⟨rate, ?_⟩
  simpa [A, final, fkRectBoundaryTransferReducedZ,
    Matrix.mulVec_mulVec] using hrate


end
end StatMech.FrontierD
