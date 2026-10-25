/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part33


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismThreeLayerRawMoment_eq_endpointAgreement
    (beta : Real) (n : Nat) (a b : Real) :
    oddPrismThreeLayerRawMoment beta n a b =
      oddPrismEndpointAgreementThreeLayerRawMoment beta n a b := by
  unfold oddPrismThreeLayerRawMoment
    oddPrismEndpointAgreementThreeLayerRawMoment
  calc
    (∑ s, ∑ v, ∑ t,
        oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n v *
          oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel a n s v *
          oddPrismPureSeamKernel b n s t) =
      ∑ s, ∑ t, ∑ v,
        oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n v *
          oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel a n s v *
          oddPrismPureSeamKernel b n s t := by
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.sum_comm]
    _ = ∑ s, ∑ t, ∑ c,
        oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate c t) *
          oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel a n s (ghsLMate c t) *
          oddPrismPureSeamKernel b n s t := by
            apply Finset.sum_congr rfl
            intro s _
            apply Finset.sum_congr rfl
            intro t _
            rw [← Equiv.sum_comp (ghsLMateEquiv t)]
            rfl
    _ = ∑ c, ∑ t, ∑ s,
        oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate c t) *
          oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel a n s (ghsLMate c t) *
          oddPrismPureSeamKernel b n s t := by
            rw [show (∑ s, ∑ t, ∑ c,
                oddPrismLayerHalfWeight beta n s ^ 2 *
                  oddPrismUpperConditionedVector beta n (ghsLMate c t) *
                  oddPrismUpperConditionedVector beta n t *
                  oddPrismPureSeamKernel a n s (ghsLMate c t) *
                  oddPrismPureSeamKernel b n s t) =
              ∑ s, ∑ c, ∑ t,
                oddPrismLayerHalfWeight beta n s ^ 2 *
                  oddPrismUpperConditionedVector beta n (ghsLMate c t) *
                  oddPrismUpperConditionedVector beta n t *
                  oddPrismPureSeamKernel a n s (ghsLMate c t) *
                  oddPrismPureSeamKernel b n s t by
                    apply Finset.sum_congr rfl
                    intro s _
                    rw [Finset.sum_comm]]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      unfold oddPrismPureSeamKernel
      let C := oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismUpperConditionedVector beta n (ghsLMate c t) *
        oddPrismUpperConditionedVector beta n t
      rw [show oddPrismLayerHalfWeight beta n s ^ 2 *
            oddPrismUpperConditionedVector beta n (ghsLMate c t) *
            oddPrismUpperConditionedVector beta n t *
            Real.exp (a * oddPrismLayerSeamInteraction n s (ghsLMate c t)) *
            Real.exp (b * oddPrismLayerSeamInteraction n s t) =
          C * (Real.exp (a * oddPrismLayerSeamInteraction n s (ghsLMate c t)) *
            Real.exp (b * oddPrismLayerSeamInteraction n s t)) by
              unfold C
              ring,
        ← Real.exp_add,
        oddPrism_twoSeamInteraction_eq_endpointAgreementCoupling]


end
end StatMech.FrontierA
