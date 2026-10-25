/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedCycle
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForceTopology
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
import Def.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition.Part2
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectPositiveBandBlockPathVertex_val
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (i : Fin (fkRectPositiveBandBulkBlocks B + 1)) :
    (fkRectPositiveBandBlockPathVertex B hheight i).1 =
      fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.start.1 := rfl


theorem fkRectPositiveBandBlockPathVertex_pair
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (i : Fin (fkRectPositiveBandBulkBlocks B)) :
    ((fkRectPositiveBandBlockPathVertex B hheight i.castSucc).1,
      (fkRectPositiveBandBlockPathVertex B hheight i.succ).1) =
    (fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.start.1,
      fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.finish.1) := by
  rw [fkRectPositiveBandBlockPathVertex_val,
    fkRectPositiveBandBlockPathVertex_val]
  congr 1
  calc
    fkRectEvenRowTranslationVertexEquiv R
        (i.succ.val * B.step) B.start.1 =
      fkRectEvenRowTranslationVertexEquiv R
        (i.val * B.step + B.step) B.start.1 := by
          rw [show i.succ.val = i.val + 1 by rfl, Nat.add_mul]
          simp
    _ = fkRectEvenRowTranslationVertexEquiv R (i.val * B.step)
        (fkRectEvenRowTranslationVertexEquiv R B.step B.start.1) :=
      (fkRectEvenRowTranslationVertexEquiv_add
        R (i.val * B.step) B.step B.start.1).symm
    _ = fkRectEvenRowTranslationVertexEquiv R
        (i.val * B.step) B.finish.1 := by rw [B.translate_start]


end
end StatMech.FrontierD
