/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierNetObstruction.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDualBarrierNetObstructionVerticalAux_winding
    (R : FKRectTorus) (n : Nat) (hn : n ≤ R.height) :
    fkRectWalkWinding R
        (fkRectDualBarrierNetObstructionVerticalAux R n) =
      (0, if n = 0 then 0 else -1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n ≤ R.height := by omega
      rw [fkRectDualBarrierNetObstructionVerticalAux,
        fkRectWalkWinding_concat, ih hn']
      simp only [Function.iterate_succ_apply']
      rw [fkRectHorizontalSeamIncrement_same_fst,
        fkRectVerticalSeamIncrement_pred]
      have hval := fkRectCyclicPred_iterate_zero_val R.height_pos n hn'
      rw [hval]
      by_cases hzero : n = 0
      · simp [hzero]
      · have hnlt : n < R.height := by omega
        simp [hzero]
        omega

end
end StatMech.FrontierD
