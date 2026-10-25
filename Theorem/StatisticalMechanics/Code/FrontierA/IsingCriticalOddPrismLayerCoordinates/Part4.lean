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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part4


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismTiltedSeamTransfer_eq_rectangularTransfer
    (beta : Real) (n : Nat) :
    oddPrismTiltedSeamTransfer beta n beta =
      rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) := by
  funext s q
  unfold oddPrismTiltedSeamTransfer oddPrismLayerHalfWeight
    oddPrismPureSeamKernel oddPrismLayerSeamInteraction
    rectangularPrismTransfer rectangularLayerVerticalInteraction
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring


theorem oddPrismTiltedSeamTransfer_eq_transfer_mul_exp
    (beta : Real) (n : Nat) (r : Real)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTiltedSeamTransfer beta n r s t =
      rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) s t *
        Real.exp ((r - beta) * oddPrismLayerSeamInteraction n s t) := by
  unfold oddPrismTiltedSeamTransfer oddPrismLayerHalfWeight
    oddPrismPureSeamKernel rectangularPrismTransfer
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  unfold oddPrismLayerSeamInteraction rectangularLayerVerticalInteraction
  congr 1
  ring


end
end StatMech.FrontierA
