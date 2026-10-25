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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part18


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismLowerConditionedVector_eq_threeLayerEndpoint
    (beta : Real) (n : Nat) (hn : 0 < n)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLowerConditionedVector beta n s =
      oddPrismLayerHalfWeight beta n s ^ 2 *
        ∑ v, oddPrismPureSeamKernel beta n s v *
          oddPrismUpperConditionedVector beta n v := by
  unfold oddPrismLowerConditionedVector
  rw [oddPrismLowerTransferTail_eq_mulVec_upper beta n hn]
  rw [← oddPrismTiltedSeamTransfer_eq_rectangularTransfer beta n]
  unfold Matrix.mulVec dotProduct oddPrismTiltedSeamTransfer
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  unfold oddPrismUpperConditionedVector
  ring


end
end StatMech.FrontierA
