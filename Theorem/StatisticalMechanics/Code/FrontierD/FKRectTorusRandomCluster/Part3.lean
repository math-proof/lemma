/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part3
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRandomClusterZ_critical_eq (R : FKRectTorus)
    {q : Real} (hq : 0 < q) :
    fkRectRandomClusterZ R (fkRectCriticalP q) q =
      (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) *
        fkRectCriticalReducedZ R q := by
  unfold fkRectRandomClusterZ fkRectCriticalReducedZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  exact fkRectRandomClusterWeight_critical_eq R hq omega

theorem fkRectCriticalReducedWeight_pos (R : FKRectTorus)
    {q : Real} (hq : 0 < q) (omega : R.Configuration) :
    0 < fkRectCriticalReducedWeight R q omega := by
  unfold fkRectCriticalReducedWeight
  exact mul_pos (pow_pos (Real.sqrt_pos.2 hq) _) (pow_pos hq _)

theorem fkRectCriticalReducedZ_pos (R : FKRectTorus)
    {q : Real} (hq : 0 < q) :
    0 < fkRectCriticalReducedZ R q := by
  unfold fkRectCriticalReducedZ
  exact Finset.sum_pos
    (fun omega _ => fkRectCriticalReducedWeight_pos R hq omega)
    Finset.univ_nonempty


end
end StatMech.FrontierD
