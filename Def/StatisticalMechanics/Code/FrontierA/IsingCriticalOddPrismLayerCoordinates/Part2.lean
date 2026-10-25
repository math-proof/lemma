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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismLayerHalfWeight (beta : Real) (n : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  Real.exp (rectangularLayerBoltzmannInteraction 1 beta s / 2)


def oddPrismUpperTransferTail (beta : Real) (n : Nat) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) -> Real :=
  (rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) ^ (n - 1)) *ᵥ
    rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1)


def oddPrismLowerTransferTail (beta : Real) (n : Nat) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) -> Real :=
  (rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) ^ n) *ᵥ
    rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1)


def oddPrismUpperConditionedVector (beta : Real) (n : Nat) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) -> Real :=
  fun s => oddPrismLayerHalfWeight beta n s *
    oddPrismUpperTransferTail beta n s


def oddPrismLowerConditionedVector (beta : Real) (n : Nat) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) -> Real :=
  fun s => oddPrismLayerHalfWeight beta n s *
    oddPrismLowerTransferTail beta n s

end
end StatMech.FrontierA
