/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectIndexedPatternPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectIndexedPatternPushforward.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCritical_cFE_pow_mul_event_le_indexedPattern_inter
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (eta : R.Configuration)
    (B : Set R.Configuration)
    (hB : FKRectDependsOnOutsideEdges R I B) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q B ≤
      fkRectCriticalEventMass R q
        (fkRectIndexedPatternEvent R I eta ∩ B) := by
  have hpre : fkRectForceIndexedPattern R I eta ⁻¹'
        (fkRectIndexedPatternEvent R I eta ∩ B) = B := by
    ext omega
    constructor
    · intro homega
      have hout : ∀ a ∉ I,
          fkRectForceIndexedPattern R I eta omega a = omega a := by
        intro a ha
        exact fkRectForceIndexedPattern_of_not_mem R eta omega ha
      exact (hB (fkRectForceIndexedPattern R I eta omega) omega hout).1
        homega.2
    · intro homega
      constructor
      · intro a ha
        exact fkRectForceIndexedPattern_of_mem R eta omega ha
      · have hout : ∀ a ∉ I,
            omega a = fkRectForceIndexedPattern R I eta omega a := by
          intro a ha
          exact (fkRectForceIndexedPattern_of_not_mem R eta omega ha).symm
        exact (hB omega (fkRectForceIndexedPattern R I eta omega) hout).1
          homega
  calc
    _ = FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q
          (fkRectForceIndexedPattern R I eta ⁻¹'
            (fkRectIndexedPatternEvent R I eta ∩ B)) := by rw [hpre]
    _ ≤ _ :=
      fkRectCritical_cFE_pow_mul_forceIndexedPattern_preimage_le_event
        R hq I eta (fkRectIndexedPatternEvent R I eta ∩ B)

end
end StatMech.FrontierD
