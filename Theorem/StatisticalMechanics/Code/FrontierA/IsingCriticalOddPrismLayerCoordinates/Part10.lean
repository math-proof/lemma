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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part10


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

@[simp] theorem rectangularPrismLayer_splitConfig_lower
    (n : Nat)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin n -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)))
    (k : Fin (n + 1)) :
    rectangularPrismLayer (oddPrismSplitLayerPathConfigEquiv n p)
        ⟨k.val, by omega⟩ = p.1 k := by
  unfold oddPrismSplitLayerPathConfigEquiv
  rw [Equiv.trans_apply, rectangularPrismLayer_equiv_symm]
  have hk := k.isLt
  have hle : k.val <= n := by omega
  simp [oddPrismLayerPathSplitEquiv, hle]

@[simp] theorem rectangularPrismLayer_splitConfig_upper
    (n : Nat)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin n -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)))
    (k : Fin n) :
    rectangularPrismLayer (oddPrismSplitLayerPathConfigEquiv n p)
        ⟨2 * n - k.val, by omega⟩ = p.2 k := by
  unfold oddPrismSplitLayerPathConfigEquiv
  rw [Equiv.trans_apply, rectangularPrismLayer_equiv_symm]
  have hk := k.isLt
  have hnot : ¬2 * n - k.val <= n := by omega
  simp [oddPrismLayerPathSplitEquiv, hnot]
  apply congrArg p.2
  apply Fin.ext
  exact Nat.sub_sub_self (by omega)


end
end StatMech.FrontierA
