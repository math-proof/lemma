/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierNetObstruction
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectDualConfigurationEquiv_dualPullbackConfiguration
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectDualConfigurationEquiv R
        (fkRectDualPullbackConfiguration R eta) = eta := by
  funext e
  rw [fkRectDualConfigurationEquiv_apply]
  simp [fkRectDualPullbackConfiguration]

theorem fkRectDualBarrierNetObstruction_dual_mem_source
    (R : FKRectTorus) :
    fkRectDualConfigurationEquiv R
        (fkRectDualBarrierNetObstructionConfiguration R) ∈
      fkRectSourceLeftBarrier R 1 (fkRectUnitLeftBarrierGap R) := by
  rw [fkRectDualBarrierNetObstructionConfiguration,
    fkRectDualConfigurationEquiv_dualPullbackConfiguration]
  exact fkRectUnitLeftBarrierConfiguration_mem_source R

theorem fkRectDualBarrierNetObstruction_vertical_open
    (R : FKRectTorus) (y : Fin R.height) :
    fkRectDualBarrierNetObstructionConfiguration R
        (true, (fkRectUnitGapColumn R, y)) = true := by
  unfold fkRectDualBarrierNetObstructionConfiguration
    fkRectDualPullbackConfiguration
  simp only [fkRectEdgeToDualEdge, Bool.true_eq, if_true]
  by_cases hy : y.val = 0
  · have hey : (false, (fkRectUnitGapColumn R, y)) =
        fkRectUnitLeftBarrierGap R := by
      rcases y with ⟨yv, hyv⟩
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · apply Fin.ext
          exact hy
    rw [hey]
    rw [fkRectAllButOneOpenSeamEvent_gap_closed R
      (fkRectUnitLeftBarrierGap_mem R)
      (fkRectUnitLeftBarrierConfiguration_seam R)]
    rfl
  · have hnot : (false, (fkRectUnitGapColumn R, y)) ∉
        fkRectHorizontalCutEdges R := by
      simpa [mem_fkRectHorizontalCutEdges_iff] using hy
    have herase : (false, (fkRectUnitGapColumn R, y)) ∉
        (fkRectHorizontalCutEdges R).erase
          (fkRectUnitLeftBarrierGap R) := by
      exact fun h => hnot (Finset.mem_erase.mp h).2
    simp [fkRectUnitLeftBarrierConfiguration,
      fkRectConfigurationOfEdges, herase]

theorem fkRectDualBarrierNetObstruction_verticalAdj
    (R : FKRectTorus) (y : Fin R.height) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Adj
        (fkRectUnitGapColumn R, y)
        (fkRectUnitGapColumn R,
          SixVertexArrows.cyclicPred R.height_pos y) := by
  refine ⟨(true, (fkRectUnitGapColumn R, y)),
    fkRectDualBarrierNetObstruction_vertical_open R y, rfl⟩

theorem fkRectDualBarrierNetObstruction_rowOneVerticalAdj
    (R : FKRectTorus) (x : Fin R.width) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Adj
        (x, (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height))
        (x, (⟨0, R.height_pos⟩ : Fin R.height)) := by
  let y1 : Fin R.height :=
    ⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩
  refine ⟨(true, (x, y1)), ?_, ?_⟩
  · unfold fkRectDualBarrierNetObstructionConfiguration
      fkRectDualPullbackConfiguration
    simp only [fkRectEdgeToDualEdge, Bool.true_eq, if_true]
    have hnot : (false, (x, y1)) ∉ fkRectHorizontalCutEdges R := by
      simp [mem_fkRectHorizontalCutEdges_iff, y1]
    have herase : (false, (x, y1)) ∉
        (fkRectHorizontalCutEdges R).erase
          (fkRectUnitLeftBarrierGap R) := by
      exact fun h => hnot (Finset.mem_erase.mp h).2
    simp [fkRectUnitLeftBarrierConfiguration,
      fkRectConfigurationOfEdges, herase]
  · have hpred : SixVertexArrows.cyclicPred R.height_pos y1 =
        (⟨0, R.height_pos⟩ : Fin R.height) := by
      apply Fin.ext
      rw [fkRectCyclicPred_val]
      simp [y1]
    simpa [fkRectTorusIndexedEdge, y1, hpred]

theorem fkRectDualBarrierNetObstruction_rowOneDiagonalAdj
    (R : FKRectTorus) (x : Fin R.width) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Adj
        (x, (⟨0, R.height_pos⟩ : Fin R.height))
        (SixVertexArrows.cyclicPred R.width_pos x,
          (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height)) := by
  let y1 : Fin R.height :=
    ⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩
  refine ⟨(false, (x, y1)), ?_, ?_⟩
  · unfold fkRectDualBarrierNetObstructionConfiguration
      fkRectDualPullbackConfiguration
    simp only [fkRectEdgeToDualEdge, Bool.false_eq_true, if_false]
    have hnot :
        (true, (SixVertexArrows.cyclicPred R.width_pos x, y1)) ∉
          fkRectHorizontalCutEdges R := by
      simp [mem_fkRectHorizontalCutEdges_iff, y1]
    have herase :
        (true, (SixVertexArrows.cyclicPred R.width_pos x, y1)) ∉
          (fkRectHorizontalCutEdges R).erase
            (fkRectUnitLeftBarrierGap R) := by
      exact fun h => hnot (Finset.mem_erase.mp h).2
    simp [fkRectUnitLeftBarrierConfiguration,
      fkRectConfigurationOfEdges, herase]
  · have hpred : SixVertexArrows.cyclicPred R.height_pos y1 =
        (⟨0, R.height_pos⟩ : Fin R.height) := by
      apply Fin.ext
      rw [fkRectCyclicPred_val]
      simp [y1]
    simp [fkRectTorusIndexedEdge, y1, hpred]

end
end StatMech.FrontierD
