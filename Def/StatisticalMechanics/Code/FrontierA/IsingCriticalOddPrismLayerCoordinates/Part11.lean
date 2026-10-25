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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part10


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismPositiveSplitLayerPathConfigEquiv (n : Nat) (hn : 0 < n) :
    ((Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1))) ≃
        RectangularPrismConfig (2 * n + 1) (2 * n + 1) n :=
  (Equiv.prodCongr (Equiv.refl _)
      (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _))).trans
    (oddPrismSplitLayerPathConfigEquiv n)

end
end StatMech.FrontierA
