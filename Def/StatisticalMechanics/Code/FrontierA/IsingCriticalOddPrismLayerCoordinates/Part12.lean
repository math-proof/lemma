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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part11


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismFullTiltedTransitionProduct (beta : Real) (n : Nat) (r : Real)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) : Real :=
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let B := oddPrismTiltedSeamTransfer beta n r
  ∏ z : Fin (2 * n), if z.val = n then
    B (rectangularPrismLayer sigma z.castSucc)
      (rectangularPrismLayer sigma z.succ)
  else
    A (rectangularPrismLayer sigma z.castSucc)
      (rectangularPrismLayer sigma z.succ)


end
end StatMech.FrontierA
