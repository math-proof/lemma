/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ScratchOddPrismVarianceOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismAgreementKernelCauchy
import Theorem.StatisticalMechanics.Code.FrontierA.ScratchOddPrismVarianceOrder


namespace StatMech.FrontierA

open StatMech StatMech.Ising

open scoped BigOperators

noncomputable section

instance oddPrismUpperBlockSite_zero_isEmpty :
    IsEmpty (OddPrismUpperBlockSite 0) :=
  ⟨by
    intro v
    have hz : v.1.z.val = 0 := by omega
    exact v.2 (by simp [oddPrismAtOrBelowCenter])⟩

end
end StatMech.FrontierA
