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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part14


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismSplitPathWeight (beta : Real) (n : Nat)
    (r : Real)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1))) : Real :=
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  transferTailPathWeight A a n p.1 *
    transferTailPathWeight A a (n - 1) p.2 *
    oddPrismTiltedSeamTransfer beta n r
      (p.1 (Fin.last n)) (p.2 (Fin.last (n - 1)))


end
end StatMech.FrontierA
