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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part20


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismUpperSlabPathWeight (beta : Real) (n k : Nat)
    (q : Fin (k + 1) ->
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  transferTailPathWeight A a k q *
    oddPrismLayerHalfWeight beta n (q (Fin.last k))


def oddPrismUpperSlabEndpointMarginal (beta : Real) (n k : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  ∑ q : Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1),
    oddPrismUpperSlabPathWeight beta n k (Fin.snoc q s)


end
end StatMech.FrontierA
