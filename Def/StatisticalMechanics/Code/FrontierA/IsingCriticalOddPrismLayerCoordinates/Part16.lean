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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part15


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismTransferBridgeVarianceNumerator
    (beta : Real) (n : Nat) (r : Real) : Real :=
  oddPrismTransferBridgeRawSecond beta n r *
      oddPrismTransferBridgeRawMoment beta n r -
    oddPrismTransferBridgeRawFirst beta n r ^ 2

def oddPrismTransferBridgeVarianceSkewNumerator
    (beta : Real) (n : Nat) (r : Real) : Real :=
  oddPrismTransferBridgeVarianceNumerator beta n r *
      oddPrismTransferBridgeRawMoment beta n (-r) ^ 2 -
    oddPrismTransferBridgeVarianceNumerator beta n (-r) *
      oddPrismTransferBridgeRawMoment beta n r ^ 2

end
end StatMech.FrontierA
