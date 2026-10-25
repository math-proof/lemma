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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part17


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismTransferPairBaseWeight (beta : Real) (n : Nat) :
    (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) -> Real :=
  fun x => oddPrismLowerConditionedVector beta n x.1 *
    oddPrismUpperConditionedVector beta n x.2

def oddPrismTransferPairInteraction (n : Nat) :
    (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) -> Real :=
  fun x => oddPrismLayerSeamInteraction n x.1 x.2


end
end StatMech.FrontierA
