/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def FKRectPositiveRowOrientedBlock.columnSuccBand
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveRowOrientedBlock R q scale)
    (hwidth : 4 * scale + 1 < R.width) :
    FKRectPositiveBandOrientedBlock R q scale := by
  let S := fkRectColumnTranslationSet R 1 B.block.carrier
  let x : S := fkRectColumnTranslationSetEquiv
    R 1 B.block.carrier B.block.start
  let y : S := fkRectColumnTranslationSetEquiv
    R 1 B.block.carrier B.block.finish
  refine
    { carrier := S
      start := x
      finish := y
      step := B.block.step
      step_even := B.block.step_even
      step_scale := B.block.step_scale
      step_upper := B.block.step_upper
      translate_start := ?_
      massFloor := B.block.massFloor
      massFloor_nonneg := B.block.massFloor_nonneg
      mass_lower := ?_
      column_bound := ?_
      row_bound := ?_ }
  · change fkRectEvenRowTranslationVertexEquiv R B.block.step
        (fkRectColumnTranslationVertexEquiv R 1 B.block.start.1) =
      fkRectColumnTranslationVertexEquiv R 1 B.block.finish.1
    rw [fkRectEvenRowTranslation_columnTranslation_comm,
      B.block.translate_start]
  · rw [show fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega B.block.carrier
          B.block.start B.block.finish} by
      simpa [S, x, y] using
        (fkRectCritical_connectedWithinMass_columnTranslation
          R 1 q B.block.carrier B.block.start B.block.finish)]
    exact B.block.mass_lower
  · intro v hv
    rcases hv with ⟨w, hw, rfl⟩
    have hwcol := B.block.column_bound w hw
    have hlt : w.1.val + 1 < R.width := by omega
    rw [fkRectColumnTranslationVertexEquiv_apply,
      fkRectColumnTranslate_one_val_of_lt R w.1 hlt]
    change 1 ≤ w.1.val + 1 ∧ w.1.val + 1 ≤ 4 * scale + 1
    omega
  · intro v hv
    rcases hv with ⟨w, hw, rfl⟩
    simpa [fkRectColumnTranslationVertexEquiv_apply] using B.row_bound w hw

end
end StatMech.FrontierD
