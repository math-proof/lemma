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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part2


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismLayerHalfWeight_pos (beta : Real) (n : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismLayerHalfWeight beta n s := by
  exact Real.exp_pos _


theorem oddPrismLowerTransferTail_eq_mulVec_upper
    (beta : Real) (n : Nat) (hn : 0 < n) :
    oddPrismLowerTransferTail beta n =
      rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) *ᵥ
        oddPrismUpperTransferTail beta n := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  funext s
  change ((A ^ n) *ᵥ a) s = (A *ᵥ (A ^ (n - 1)) *ᵥ a) s
  have hpow : A ^ n = A * A ^ (n - 1) := by
    calc
      A ^ n = A ^ ((n - 1) + 1) := by congr 1; omega
      _ = A * A ^ (n - 1) := pow_succ' A (n - 1)
  rw [hpow, ← Matrix.mulVec_mulVec]


theorem oddPrismLowerConditionedVector_eq_transfer_upper
    (beta : Real) (n : Nat) (hn : 0 < n) :
    oddPrismLowerConditionedVector beta n = fun s =>
      oddPrismLayerHalfWeight beta n s *
        (rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) *ᵥ
          (fun q => oddPrismUpperConditionedVector beta n q /
            oddPrismLayerHalfWeight beta n q)) s := by
  funext s
  unfold oddPrismLowerConditionedVector
  rw [oddPrismLowerTransferTail_eq_mulVec_upper beta n hn]
  congr 1
  congr 1
  funext q
  unfold oddPrismUpperConditionedVector
  rw [mul_div_cancel_left₀]
  exact (oddPrismLayerHalfWeight_pos beta n q).ne'


end
end StatMech.FrontierA
