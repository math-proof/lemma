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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part29


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismTransferBridgeVariance_eq_sum_covarianceRows
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n r =
      ∑ p, oddPrismTransferTiltedPairCovarianceRow beta n r p := by
  rw [oddPrismTransferBridgeVariance_eq_pairProbVariance]
  unfold oddPrismTransferTiltedPairCovarianceRow
    oddPrismTransferPairAgreementSpin
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    unfold oddPrismTransferPairInteraction oddPrismLayerSeamInteraction
    ring
  · rw [← Finset.sum_mul]
    rw [pow_two]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    unfold oddPrismTransferPairInteraction oddPrismLayerSeamInteraction
    rw [Finset.mul_sum]

theorem oddPrismTransferBridgeFlippedVariance_eq_sum_covarianceRows
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeFlippedVariance beta n r =
      ∑ p, oddPrismTransferFlippedTiltedPairCovarianceRow beta n r p := by
  rw [oddPrismTransferBridgeFlippedVariance_eq_pairProbVariance]
  unfold oddPrismTransferFlippedTiltedPairCovarianceRow
    oddPrismTransferPairAgreementSpin
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    unfold oddPrismTransferPairInteraction oddPrismLayerSeamInteraction
    ring
  · rw [← Finset.sum_mul]
    rw [pow_two]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    unfold oddPrismTransferPairInteraction oddPrismLayerSeamInteraction
    rw [Finset.mul_sum]


theorem oddPrismTransferBridgeVariance_le_neg_of_covarianceRows
    (beta : Real) (n : Nat) (r : Real)
    (hrow : ∀ p,
      oddPrismTransferTiltedPairCovarianceRow beta n r p <=
        oddPrismTransferFlippedTiltedPairCovarianceRow beta n r p) :
    oddPrismTransferBridgeVariance beta n r <=
      oddPrismTransferBridgeVariance beta n (-r) := by
  rw [oddPrismTransferBridgeVariance_neg_eq_flipped,
    oddPrismTransferBridgeVariance_eq_sum_covarianceRows,
    oddPrismTransferBridgeFlippedVariance_eq_sum_covarianceRows]
  exact Finset.sum_le_sum fun p _ => hrow p


end
end StatMech.FrontierA
