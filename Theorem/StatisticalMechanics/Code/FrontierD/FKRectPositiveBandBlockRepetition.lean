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
import Def.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem FKRectPositiveBandOrientedBlock.step_pos
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hscale : 3 ≤ scale) :
    0 < B.step := by
  have hbound := B.step_scale
  omega

theorem fkRectPositiveBandBulkBlocks_mul_step_le
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale) :
    fkRectPositiveBandBulkBlocks B * B.step ≤
      R.height - 1 - (24 * scale + 4) := by
  exact Nat.div_mul_le_self _ _

theorem fkRectPositiveBandBulkBlocks_remainder_lt
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hscale : 3 ≤ scale) :
    R.height - 1 - (24 * scale + 4) -
        fkRectPositiveBandBulkBlocks B * B.step < B.step := by
  let N := R.height - 1 - (24 * scale + 4)
  have hstep := B.step_pos hscale
  have hdecomp : N % B.step + N / B.step * B.step = N := by
    simpa [Nat.mul_comm] using Nat.mod_add_div N B.step
  have hmod : N % B.step < B.step := Nat.mod_lt N hstep
  have hle : N / B.step * B.step ≤ N := Nat.div_mul_le_self _ _
  have hsub : N - N / B.step * B.step = N % B.step := by omega
  change N - N / B.step * B.step < B.step
  rw [hsub]
  exact hmod


end
end StatMech.FrontierD
