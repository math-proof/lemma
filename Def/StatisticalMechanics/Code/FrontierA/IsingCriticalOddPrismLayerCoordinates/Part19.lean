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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part18


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismThreeLayerRawMoment
    (beta : Real) (n : Nat) (a b : Real) : Real :=
  ∑ s, ∑ v, ∑ t,
    oddPrismLayerHalfWeight beta n s ^ 2 *
      oddPrismUpperConditionedVector beta n v *
      oddPrismUpperConditionedVector beta n t *
      oddPrismPureSeamKernel a n s v *
      oddPrismPureSeamKernel b n s t

def oddPrismThreeLayerWeight
    (beta : Real) (n : Nat) (a b : Real)
    (s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  oddPrismLayerHalfWeight beta n s ^ 2 *
    oddPrismUpperConditionedVector beta n v *
    oddPrismUpperConditionedVector beta n t *
    oddPrismPureSeamKernel a n s v *
    oddPrismPureSeamKernel b n s t


end
end StatMech.FrontierA
