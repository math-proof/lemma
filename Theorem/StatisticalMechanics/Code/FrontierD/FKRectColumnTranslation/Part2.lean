/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part2
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectColumnTranslationEquiv_apply
    (R : FKRectTorus) (s : Int) (x : Fin R.width) :
    fkRectColumnTranslationEquiv R s x = fkRectColumnTranslate R s x := rfl

theorem fkRectColumn_cyclicPred_cast (R : FKRectTorus)
    (x : Fin R.width) :
    ((SixVertexArrows.cyclicPred R.width_pos x).val : ZMod R.width) =
      (x.val : ZMod R.width) - 1 := by
  rw [fkRectCyclicPred_val]
  split <;> rename_i h
  · rw [Nat.cast_sub (by omega : 1 ≤ R.width)]
    push_cast
    rw [h]
    simp
  · rw [Nat.cast_sub (by omega : 1 ≤ x.val)]
    push_cast
    ring

theorem fkRectColumnTranslate_cyclicPred
    (R : FKRectTorus) (s : Int) (x : Fin R.width) :
    fkRectColumnTranslate R s
        (SixVertexArrows.cyclicPred R.width_pos x) =
      SixVertexArrows.cyclicPred R.width_pos
        (fkRectColumnTranslate R s x) := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.width).mp
    rw [show ((fkRectColumnTranslate R s
        (SixVertexArrows.cyclicPred R.width_pos x)).val : ZMod R.width) =
        (SixVertexArrows.cyclicPred R.width_pos x).val + s by
      simpa [fkRectColumnTranslate] using fkRectIntModFin_cast R.width_pos
        ((SixVertexArrows.cyclicPred R.width_pos x).val + s)]
    rw [fkRectColumn_cyclicPred_cast, fkRectColumn_cyclicPred_cast]
    rw [show ((fkRectColumnTranslate R s x).val : ZMod R.width) =
        (x.val : Int) + s by
      simpa [fkRectColumnTranslate] using fkRectIntModFin_cast R.width_pos
        ((x.val : Int) + s)]
    push_cast
    ring
  · exact (fkRectColumnTranslate R s
      (SixVertexArrows.cyclicPred R.width_pos x)).isLt
  · exact (SixVertexArrows.cyclicPred R.width_pos
      (fkRectColumnTranslate R s x)).isLt


end
end StatMech.FrontierD
