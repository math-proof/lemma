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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part39
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectConfigurationStripSeamGraph_component_count
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card
        (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent =
      fkRectBoundaryTransferClusterCount R omega := by
  have h := fkRectStripSeamGraph_component_count R.width_pos
    (R.height - 1) (fkRectConfigurationNonSeamLayerFn R omega)
    (fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R))
  rw [Nat.card_eq_fintype_card] at h
  rw [fkRectStripClosedCount_eq_runClosedCount,
    fkRectStripState_eq_runState] at h
  simpa [fkRectConfigurationStripSeamGraph,
    fkRectBoundaryTransferClusterCount,
    fkRectConfigurationFinalBoundaryState] using h

theorem fkRectConfigurationStripSeamGraph_component_count_eq_numClusters
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card
        (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  exact Fintype.card_congr
    (fkRectConfigurationStripSeamIso R omega).connectedComponentEquiv

theorem fkRectBoundaryTransferClusterCount_eq_numClusters
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectBoundaryTransferClusterCount R omega =
      fkRectNumClusters R omega := by
  rw [← fkRectConfigurationStripSeamGraph_component_count R omega]
  exact fkRectConfigurationStripSeamGraph_component_count_eq_numClusters R omega

theorem fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight
    (R : FKRectTorus) (q : Real) (omega : R.Configuration) :
    fkRectBoundaryTransferCoefficient R q omega =
      fkRectCriticalReducedWeight R q omega := by
  rw [fkRectBoundaryTransferCoefficient_eq,
    fkRectBoundaryTransferClusterCount_eq_numClusters]
  rfl

theorem fkRectBoundaryTransferClusterCount_eq_numClusters_of_geometry
    (R : FKRectTorus) (omega : R.Configuration)
    (hgeometry : Fintype.card
        (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent =
      fkRectNumClusters R omega) :
    fkRectBoundaryTransferClusterCount R omega =
      fkRectNumClusters R omega := by
  rw [← fkRectConfigurationStripSeamGraph_component_count R omega]
  exact hgeometry

theorem fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight_of_geometry
    (R : FKRectTorus) (q : Real) (omega : R.Configuration)
    (hgeometry : Fintype.card
        (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent =
      fkRectNumClusters R omega) :
    fkRectBoundaryTransferCoefficient R q omega =
      fkRectCriticalReducedWeight R q omega := by
  rw [fkRectBoundaryTransferCoefficient_eq,
    fkRectBoundaryTransferClusterCount_eq_numClusters_of_geometry
      R omega hgeometry]
  rfl

theorem fkRectBoundaryLayerWeight_pos {W : Nat} (hW : 0 < W)
    {q : Real} (hq : 0 < q) (evenRow : Bool)
    (state : FKRectBoundaryState W) (eta : Bool × Fin W -> Bool) :
    0 < fkRectBoundaryLayerWeight hW q evenRow state eta := by
  unfold fkRectBoundaryLayerWeight
  exact mul_pos (pow_pos (Real.sqrt_pos.2 hq) _) (pow_pos hq _)

theorem fkRectBoundaryLayerTransfer_nonneg {W : Nat} (hW : 0 < W)
    {q : Real} (hq : 0 < q) (evenRow : Bool)
    (source target : FKRectBoundaryState W) :
    0 <= fkRectBoundaryLayerTransfer hW q evenRow source target := by
  classical
  unfold fkRectBoundaryLayerTransfer
  exact Finset.sum_nonneg fun eta _ => by
    split_ifs
    · exact (fkRectBoundaryLayerWeight_pos hW hq evenRow source eta).le
    · exact le_rfl


theorem fkRectBoundaryLayerTransfer_target_isConnectivity_of_pos
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (evenRow : Bool) (source target : FKRectBoundaryState W)
    (hpos : 0 < fkRectBoundaryLayerTransfer hW q evenRow source target) :
    target.IsConnectivity := by
  classical
  unfold fkRectBoundaryLayerTransfer at hpos
  rw [Finset.sum_pos_iff_of_nonneg] at hpos
  · obtain ⟨eta, heta, hterm⟩ := hpos
    split at hterm <;> simp_all
    subst target
    exact fkRectBoundaryLayerOutput_isConnectivity hW evenRow source eta
  · intro eta heta
    split_ifs
    · exact (fkRectBoundaryLayerWeight_pos hW hq evenRow source eta).le
    · exact le_rfl

theorem fkRectBoundaryTwoLayerTransfer_nonneg {W : Nat} (hW : 0 < W)
    {q : Real} (hq : 0 < q) (source target : FKRectBoundaryState W) :
    0 ≤ fkRectBoundaryTwoLayerTransfer hW q source target := by
  unfold fkRectBoundaryTwoLayerTransfer
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun middle _ => mul_nonneg
    (fkRectBoundaryLayerTransfer_nonneg hW hq false source middle)
    (fkRectBoundaryLayerTransfer_nonneg hW hq true middle target)


theorem fkRectBoundaryTwoLayerTransfer_target_isConnectivity_of_pos
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (source target : FKRectBoundaryState W)
    (hpos : 0 < fkRectBoundaryTwoLayerTransfer hW q source target) :
    target.IsConnectivity := by
  classical
  unfold fkRectBoundaryTwoLayerTransfer at hpos
  rw [Matrix.mul_apply, Finset.sum_pos_iff_of_nonneg] at hpos
  · obtain ⟨middle, hmiddle, hproduct⟩ := hpos
    have hright : 0 < fkRectBoundaryLayerTransfer hW q true middle target := by
      have hleft := fkRectBoundaryLayerTransfer_nonneg hW hq false source middle
      have hright := fkRectBoundaryLayerTransfer_nonneg hW hq true middle target
      nlinarith
    exact fkRectBoundaryLayerTransfer_target_isConnectivity_of_pos
      hW hq true middle target hright
  · intro middle hmiddle
    exact mul_nonneg
      (fkRectBoundaryLayerTransfer_nonneg hW hq false source middle)
      (fkRectBoundaryLayerTransfer_nonneg hW hq true middle target)


end
end StatMech.FrontierD
