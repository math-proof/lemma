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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part5


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismTransferBridgeFlippedRawMoment
    (beta : Real) (n : Nat) (r : Real) : Real :=
  ∑ s, ∑ q,
    oddPrismLowerConditionedVector beta n s *
      oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV q) *
      oddPrismPureSeamKernel r n s q

def oddPrismTransferBridgeFlippedRawFirst
    (beta : Real) (n : Nat) (r : Real) : Real :=
  ∑ s, ∑ q,
    oddPrismLowerConditionedVector beta n s *
      oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV q) *
      (oddPrismLayerSeamInteraction n s q *
        oddPrismPureSeamKernel r n s q)

def oddPrismTransferBridgeFlippedRawSecond
    (beta : Real) (n : Nat) (r : Real) : Real :=
  ∑ s, ∑ q,
    oddPrismLowerConditionedVector beta n s *
      oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV q) *
      (oddPrismLayerSeamInteraction n s q ^ 2 *
        oddPrismPureSeamKernel r n s q)

def oddPrismTransferBridgeFlippedVariance
    (beta : Real) (n : Nat) (r : Real) : Real :=
  oddPrismTransferBridgeFlippedRawSecond beta n r /
      oddPrismTransferBridgeFlippedRawMoment beta n r -
    (oddPrismTransferBridgeFlippedRawFirst beta n r /
      oddPrismTransferBridgeFlippedRawMoment beta n r) ^ 2

end
end StatMech.FrontierA
