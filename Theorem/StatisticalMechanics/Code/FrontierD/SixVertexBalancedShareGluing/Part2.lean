/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetNormalization.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBalancedShareGluing.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBalancedSectorShare_negLog_le_fourCopyCost
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    -Real.log (fkRectBalancedSectorShare R q) <=
      fkRectFourCopyShareCost R q := by
  exact fkRectBalancedSectorShare_negLog_le_fourCopy R hq


theorem tendsto_balancedShare_negLog_div_height_zero_of_fourCopyCost
    (R : Nat -> FKRectTorus) {q : Real} (hq : 4 < q)
    (hcost : Tendsto (fun n =>
      fkRectFourCopyShareCost (R n) q / (R n).height)
        atTop (nhds 0)) :
    Tendsto (fun n =>
      -Real.log (fkRectBalancedSectorShare (R n) q) / (R n).height)
        atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n =>
      -Real.log (fkRectBalancedSectorShare (R n) q) / (R n).height)
    tendsto_const_nhds hcost
  · filter_upwards [] with n
    apply div_nonneg
    · rw [neg_nonneg]
      exact Real.log_nonpos
        (fkRectBalancedSectorShare_mem_Ioc (R n) hq).1.le
        (fkRectBalancedSectorShare_mem_Ioc (R n) hq).2
    · positivity
  · filter_upwards [] with n
    apply div_le_div_of_nonneg_right
      (fkRectBalancedSectorShare_negLog_le_fourCopyCost (R n) hq)
    positivity


theorem tendsto_balancedNormalization_negLog_div_height_zero_of_all_and_fourCopy
    (R : Nat -> FKRectTorus) {q : Real} (hq : 4 < q)
    (hall : Tendsto (fun n =>
      -Real.log (fkRectAllSectorNormalization (R n) q) / (R n).height)
        atTop (nhds 0))
    (hcost : Tendsto (fun n =>
      fkRectFourCopyShareCost (R n) q / (R n).height)
        atTop (nhds 0)) :
    Tendsto (fun n =>
      -Real.log (fkRectBalancedSectorNormalization (R n) q) /
        (R n).height) atTop (nhds 0) := by
  have hshare :=
    tendsto_balancedShare_negLog_div_height_zero_of_fourCopyCost R hq hcost
  have hadd := hall.add hshare
  have htarget : Tendsto (fun n =>
      -Real.log (fkRectBalancedSectorNormalization (R n) q) /
        (R n).height) atTop (nhds (0 + 0)) := by
    apply hadd.congr'
    filter_upwards [] with n
    rw [balancedNormalization_negLog_eq_all_add_share (R n) hq]
    ring
  simpa using htarget

end
end StatMech.FrontierD
