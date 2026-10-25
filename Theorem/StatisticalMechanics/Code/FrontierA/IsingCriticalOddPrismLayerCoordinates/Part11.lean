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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part11


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

@[simp] theorem rectangularPrismLayer_positiveSplitConfig_lower
    (n : Nat) (hn : 0 < n)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1)))
    (k : Fin (n + 1)) :
    rectangularPrismLayer (oddPrismPositiveSplitLayerPathConfigEquiv n hn p)
        ⟨k.val, by omega⟩ = p.1 k := by
  unfold oddPrismPositiveSplitLayerPathConfigEquiv
  rw [Equiv.trans_apply, rectangularPrismLayer_splitConfig_lower]
  rfl

@[simp] theorem rectangularPrismLayer_positiveSplitConfig_upper
    (n : Nat) (hn : 0 < n)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1)))
    (k : Fin (n - 1 + 1)) :
    rectangularPrismLayer (oddPrismPositiveSplitLayerPathConfigEquiv n hn p)
        ⟨2 * n - k.val, by omega⟩ = p.2 k := by
  unfold oddPrismPositiveSplitLayerPathConfigEquiv
  rw [Equiv.trans_apply]
  have h := rectangularPrismLayer_splitConfig_upper n
    ((Equiv.prodCongr (Equiv.refl _)
      (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _))) p)
    ((finCongr (by omega)) k)
  simpa using h


end
end StatMech.FrontierA
