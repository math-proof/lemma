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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectPositiveBandBlockPathVertex
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (i : Fin (fkRectPositiveBandBulkBlocks B + 1)) :
    FKRectColumnBandVertex R 1 (4 * scale + 1) 1 (R.height - 1) := by
  let v := fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.start.1
  refine ⟨v, ?_⟩
  have hmul := fkRectPositiveBandBulkBlocks_mul_step_le B
  have hi : i.val ≤ fkRectPositiveBandBulkBlocks B := by omega
  have himul : i.val * B.step ≤
      fkRectPositiveBandBulkBlocks B * B.step :=
    Nat.mul_le_mul_right B.step hi
  have hrow := B.row_bound B.start.1 B.start.2
  have hlt : B.start.1.2.val + i.val * B.step < R.height := by
    have hrecover :
        R.height - 1 - (24 * scale + 4) + (24 * scale + 4) =
          R.height - 1 := Nat.sub_add_cancel hheight
    omega
  have htranslate := fkRectRowTranslate_eq_add_of_lt
    R (i.val * B.step) B.start.1.2 hlt
  change 1 ≤ v.1.val ∧ v.1.val ≤ 4 * scale + 1 ∧
    1 ≤ v.2.val ∧ v.2.val ≤ R.height - 1
  dsimp [v]
  rw [show fkRectRowTranslate R
      ((i.val : Int) * (B.step : Int)) B.start.1.2 =
        ⟨B.start.1.2.val + i.val * B.step, hlt⟩ by
      simpa [Nat.cast_mul] using htranslate]
  refine ⟨(B.column_bound B.start.1 B.start.2).1,
    (B.column_bound B.start.1 B.start.2).2, ?_, ?_⟩
  · exact hrow.1.trans (Nat.le_add_right _ _)
  · exact Nat.le_sub_one_of_lt hlt

end
end StatMech.FrontierD
