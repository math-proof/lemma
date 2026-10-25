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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part32


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismEndpointAgreementThreeLayerRawMoment
    (beta : Real) (n : Nat) (a b : Real) : Real :=
  ∑ c, ∑ t, ∑ s,
    oddPrismLayerHalfWeight beta n s ^ 2 *
      oddPrismUpperConditionedVector beta n (ghsLMate c t) *
      oddPrismUpperConditionedVector beta n t *
      Real.exp (∑ p, (b + a * spin c p) * (spin s p * spin t p))

end
end StatMech.FrontierA
