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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part5


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismTransferBridgeRawMoment_eq_tailContraction
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      ∑ s, oddPrismLowerTransferTail beta n s *
        (oddPrismTiltedSeamTransfer beta n r *ᵥ
          oddPrismUpperTransferTail beta n) s := by
  unfold oddPrismTransferBridgeRawMoment
    oddPrismLowerConditionedVector oddPrismUpperConditionedVector
    oddPrismTiltedSeamTransfer Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring


theorem oddPrismTransferBridgeRawMoment_eq_oneStepContraction
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      ∑ s,
        (rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) *ᵥ
          oddPrismUpperTransferTail beta n) s *
        (oddPrismTiltedSeamTransfer beta n r *ᵥ
          oddPrismUpperTransferTail beta n) s := by
  rw [oddPrismTransferBridgeRawMoment_eq_tailContraction]
  rw [oddPrismLowerTransferTail_eq_mulVec_upper beta n hn]


end
end StatMech.FrontierA
