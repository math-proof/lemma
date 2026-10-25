/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierNetObstruction.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDualBarrierNetObstructionHorizontalAux_winding
    (R : FKRectTorus) (n : Nat) (hn : n ≤ R.width) :
    fkRectWalkWinding R
        (fkRectDualBarrierNetObstructionHorizontalAux R n) =
      (if n = 0 then 0 else -1, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n ≤ R.width := by omega
      rw [fkRectDualBarrierNetObstructionHorizontalAux,
        fkRectWalkWinding_concat, fkRectWalkWinding_concat, ih hn']
      simp only [Function.iterate_succ_apply']
      have hfirstVertical :
          fkRectVerticalSeamIncrement R
            (((SixVertexArrows.cyclicPred R.width_pos)^[n]
                (⟨0, R.width_pos⟩ : Fin R.width),
              (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height)))
            (((SixVertexArrows.cyclicPred R.width_pos)^[n]
                (⟨0, R.width_pos⟩ : Fin R.width),
              (⟨0, R.height_pos⟩ : Fin R.height))) = 0 := by
        unfold fkRectVerticalSeamIncrement
        have hheight := R.height_gt_two
        simp
        omega
      have hdiagVertical :
          fkRectVerticalSeamIncrement R
            (((SixVertexArrows.cyclicPred R.width_pos)^[n]
                (⟨0, R.width_pos⟩ : Fin R.width),
              (⟨0, R.height_pos⟩ : Fin R.height)))
            (SixVertexArrows.cyclicPred R.width_pos
                ((SixVertexArrows.cyclicPred R.width_pos)^[n]
                  (⟨0, R.width_pos⟩ : Fin R.width)),
              (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height)) = 0 := by
        apply fkRectVerticalSeamIncrement_eq_zero_of_not_crosses
        rw [fkRectCrossesVerticalSeam_mk]
        have hheight := R.height_gt_two
        simp
        omega
      rw [fkRectHorizontalSeamIncrement_same_fst, hfirstVertical,
        fkRectHorizontalSeamIncrement_pred, hdiagVertical]
      have hval := fkRectCyclicPred_iterate_zero_val R.width_pos n hn'
      rw [hval]
      by_cases hzero : n = 0
      · simp [hzero]
      · have hnlt : n < R.width := by omega
        simp [hzero]
        omega

end
end StatMech.FrontierD
