/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part4
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

def fkRectCriticalRandomClusterPMF (R : FKRectTorus)
    {q : Real} (hq : 0 < q) : PMF R.Configuration :=
  PMF.ofFintype
    (fun omega => ENNReal.ofReal (fkRectCriticalRandomClusterProb R q omega)) <| by
      rw [<- ENNReal.ofReal_sum_of_nonneg
        (fun omega _ => fkRectCriticalRandomClusterProb_nonneg R hq omega),
        sum_fkRectCriticalRandomClusterProb R hq]
      simp

end
end StatMech.FrontierD
