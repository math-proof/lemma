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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part28


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismTransferTiltedPairCovarianceRow
    (beta : Real) (n : Nat) (r : Real)
    (p : Fin (2 * n + 1) × Fin (2 * n + 1)) : Real :=
  (∑ x, oddPrismTransferTiltedPairProb beta n r x *
      (oddPrismTransferPairAgreementSpin n p x *
        oddPrismTransferPairInteraction n x)) -
    (∑ x, oddPrismTransferTiltedPairProb beta n r x *
      oddPrismTransferPairAgreementSpin n p x) *
    (∑ x, oddPrismTransferTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x)


def oddPrismTransferFlippedTiltedPairCovarianceRow
    (beta : Real) (n : Nat) (r : Real)
    (p : Fin (2 * n + 1) × Fin (2 * n + 1)) : Real :=
  (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
      (oddPrismTransferPairAgreementSpin n p x *
        oddPrismTransferPairInteraction n x)) -
    (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
      oddPrismTransferPairAgreementSpin n p x) *
    (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x)

end
end StatMech.FrontierA
