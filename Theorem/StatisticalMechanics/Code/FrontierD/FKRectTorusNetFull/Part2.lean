/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectFullOpenGraph_adj_verticalPred (R : FKRectTorus)
    (x : Fin R.width) (y : Fin R.height) :
    (fkRectFullOpenGraph R).Adj (x, y)
      (x, SixVertexArrows.cyclicPred R.height_pos y) := by
  change (fkRectOpenGraph R
    (fkRectConfigurationOfEdges R Finset.univ)).Adj _ _
  rw [fkRectOpenGraph_configurationOfEdges_univ]
  exact fkRectTorusGraph_adj_verticalPred R x y

theorem fkRectFullOpenGraph_adj_horizontalPred_diag_zero (R : FKRectTorus)
    (x : Fin R.width) :
    (fkRectFullOpenGraph R).Adj
      (x, (⟨0, R.height_pos⟩ : Fin R.height))
      (SixVertexArrows.cyclicPred R.width_pos x,
        SixVertexArrows.cyclicPred R.height_pos
          (⟨0, R.height_pos⟩ : Fin R.height)) := by
  change (fkRectOpenGraph R
    (fkRectConfigurationOfEdges R Finset.univ)).Adj _ _
  rw [fkRectOpenGraph_configurationOfEdges_univ]
  refine ⟨(false, (x, (⟨0, R.height_pos⟩ : Fin R.height))), ?_⟩
  simp [fkRectTorusIndexedEdge]

theorem fkRectHorizontalSeamIncrement_same_fst (R : FKRectTorus)
    (x : Fin R.width) (y z : Fin R.height) :
    fkRectHorizontalSeamIncrement R (x, y) (x, z) = 0 := by
  have hwidth := R.width_gt_two
  unfold fkRectHorizontalSeamIncrement
  change (if x.val + 1 = R.width ∧ x.val = 0 then 1
    else if x.val = 0 ∧ x.val + 1 = R.width then -1 else 0) = 0
  split <;> rename_i h
  · omega
  · split <;> rename_i h'
    · omega
    · rfl

theorem fkRectVerticalSeamIncrement_same_snd (R : FKRectTorus)
    (x z : Fin R.width) (y : Fin R.height) :
    fkRectVerticalSeamIncrement R (x, y) (z, y) = 0 := by
  have hheight := R.height_gt_two
  unfold fkRectVerticalSeamIncrement
  change (if y.val + 1 = R.height ∧ y.val = 0 then 1
    else if y.val = 0 ∧ y.val + 1 = R.height then -1 else 0) = 0
  split <;> rename_i h
  · omega
  · split <;> rename_i h'
    · omega
    · rfl

theorem fkRectHorizontalSeamIncrement_pred (R : FKRectTorus)
    (x : Fin R.width) (y z : Fin R.height) :
    fkRectHorizontalSeamIncrement R (x, y)
      (SixVertexArrows.cyclicPred R.width_pos x, z) =
        if x.val = 0 then -1 else 0 := by
  have hwidth := R.width_gt_two
  have hxlt := x.isLt
  unfold fkRectHorizontalSeamIncrement
  rw [show (SixVertexArrows.cyclicPred R.width_pos x).val =
      if x.val = 0 then R.width - 1 else x.val - 1 from
    fkRectCyclicPred_val R.width_pos x]
  by_cases hx : x.val = 0
  · have hsecond : R.width - 1 + 1 = R.width := by omega
    simp [hx, hsecond]
    omega
  · have hfirst : ¬ (x.val + 1 = R.width ∧ x.val - 1 = 0) := by
      omega
    simp [hx, hfirst]

theorem fkRectVerticalSeamIncrement_pred (R : FKRectTorus)
    (x z : Fin R.width) (y : Fin R.height) :
    fkRectVerticalSeamIncrement R (x, y)
      (z, SixVertexArrows.cyclicPred R.height_pos y) =
        if y.val = 0 then -1 else 0 := by
  have hheight := R.height_gt_two
  have hylt := y.isLt
  unfold fkRectVerticalSeamIncrement
  rw [show (SixVertexArrows.cyclicPred R.height_pos y).val =
      if y.val = 0 then R.height - 1 else y.val - 1 from
    fkRectCyclicPred_val R.height_pos y]
  by_cases hy : y.val = 0
  · have hsecond : R.height - 1 + 1 = R.height := by omega
    simp [hy, hsecond]
    omega
  · have hfirst : ¬ (y.val + 1 = R.height ∧ y.val - 1 = 0) := by
      omega
    simp [hy, hfirst]

theorem fkRectVerticalSeamIncrement_pred_zero (R : FKRectTorus)
    (x z : Fin R.width) :
    fkRectVerticalSeamIncrement R
      (x, (⟨0, R.height_pos⟩ : Fin R.height))
      (z, SixVertexArrows.cyclicPred R.height_pos
        (⟨0, R.height_pos⟩ : Fin R.height)) = -1 := by
  rw [fkRectVerticalSeamIncrement_pred]
  simp

theorem fkRectVerticalSeamIncrement_pred_zero_reverse (R : FKRectTorus)
    (x z : Fin R.width) :
    fkRectVerticalSeamIncrement R
      (z, SixVertexArrows.cyclicPred R.height_pos
        (⟨0, R.height_pos⟩ : Fin R.height))
      (x, (⟨0, R.height_pos⟩ : Fin R.height)) = 1 := by
  rw [fkRectVerticalSeamIncrement_swap,
    fkRectVerticalSeamIncrement_pred_zero]
  norm_num

end
end StatMech.FrontierD
