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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part9


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismLayerPathSplitEquiv (E : Type*) (n : Nat) :
    (Fin (2 * n + 1) -> E) ≃
      ((Fin (n + 1) -> E) × (Fin n -> E)) where
  toFun q :=
    (fun k => q ⟨k.val, by omega⟩,
      fun k => q ⟨2 * n - k.val, by omega⟩)
  invFun p := fun z =>
    if hz : z.val <= n then p.1 ⟨z.val, by omega⟩
    else p.2 ⟨2 * n - z.val, by
      have hzLt := z.isLt
      omega⟩
  left_inv q := by
    funext z
    by_cases hz : z.val <= n
    · simp [hz]
    · simp [hz]
      congr
      have hzLt := z.isLt
      omega
  right_inv p := by
    apply Prod.ext
    · funext k
      have hk := k.isLt
      have hle : k.val <= n := by omega
      simp [hle]
    · funext k
      have hk := k.isLt
      have hnot : ¬2 * n - k.val <= n := by omega
      simp [hnot]
      apply congrArg p.2
      apply Fin.ext
      exact Nat.sub_sub_self (by omega)


def oddPrismSplitLayerPathConfigEquiv (n : Nat) :
    ((Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin n -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) ≃
        RectangularPrismConfig (2 * n + 1) (2 * n + 1) n :=
  (oddPrismLayerPathSplitEquiv
      (RectangularLayerConfig (2 * n + 1) (2 * n + 1)) n).symm.trans
    (rectangularPrismLayerEquiv (2 * n + 1) (2 * n + 1) n).symm

end
end StatMech.FrontierA
