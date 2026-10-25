/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part4
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCriticalRandomClusterProb_eq_weight_div_Z
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q omega =
      fkRectRandomClusterWeight R (fkRectCriticalP q) q omega /
        fkRectRandomClusterZ R (fkRectCriticalP q) q := by
  rw [fkRectCriticalRandomClusterProb,
    fkRectRandomClusterWeight_critical_eq R hq,
    fkRectRandomClusterZ_critical_eq R hq]
  have hd : (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) ≠ 0 := by
    positivity
  field_simp

theorem fkRectCriticalRandomClusterProb_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    0 <= fkRectCriticalRandomClusterProb R q omega := by
  exact (div_pos (fkRectCriticalReducedWeight_pos R hq omega)
    (fkRectCriticalReducedZ_pos R hq)).le

theorem sum_fkRectCriticalRandomClusterProb
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    ∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega = 1 := by
  unfold fkRectCriticalRandomClusterProb
  rw [<- Finset.sum_div]
  exact div_self (fkRectCriticalReducedZ_pos R hq).ne'


end
end StatMech.FrontierD
