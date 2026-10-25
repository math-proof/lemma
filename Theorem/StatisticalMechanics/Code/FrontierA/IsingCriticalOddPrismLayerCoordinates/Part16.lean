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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part16


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismTransferBridgeRawMoment_pos
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    0 < oddPrismTransferBridgeRawMoment beta n r := by
  rw [← oddPrismGraphBridgeRawMoment_eq_transfer beta n hn r]
  exact oddPrismGraphBridgeRawMoment_pos beta n r


theorem oddPrismTransferBridgeVariance_eq_numerator_div
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismTransferBridgeVariance beta n r =
      oddPrismTransferBridgeVarianceNumerator beta n r /
        oddPrismTransferBridgeRawMoment beta n r ^ 2 := by
  have hp := (oddPrismTransferBridgeRawMoment_pos beta n hn r).ne'
  unfold oddPrismTransferBridgeVariance
    oddPrismTransferBridgeVarianceNumerator
  field_simp


theorem hasDerivAt_oddPrismTransferBridgeLogRawMoment
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    HasDerivAt
      (fun t => Real.log (oddPrismTransferBridgeRawMoment beta n t))
      (oddPrismTransferBridgeRawFirst beta n r /
        oddPrismTransferBridgeRawMoment beta n r) r := by
  exact (hasDerivAt_oddPrismTransferBridgeRawMoment beta n r).log
    (oddPrismTransferBridgeRawMoment_pos beta n hn r).ne'

theorem hasDerivAt_oddPrismTransferBridgeLogDerivative
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    HasDerivAt
      (fun t => oddPrismTransferBridgeRawFirst beta n t /
        oddPrismTransferBridgeRawMoment beta n t)
      (oddPrismTransferBridgeVariance beta n r) r := by
  have h := (hasDerivAt_oddPrismTransferBridgeRawFirst beta n r).div
    (hasDerivAt_oddPrismTransferBridgeRawMoment beta n r)
    (oddPrismTransferBridgeRawMoment_pos beta n hn r).ne'
  convert h using 1
  unfold oddPrismTransferBridgeVariance
  field_simp


theorem oddPrismTransferBridgeVariance_le_neg_iff_skewNumerator_nonpos
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismTransferBridgeVariance beta n r <=
        oddPrismTransferBridgeVariance beta n (-r) ↔
      oddPrismTransferBridgeVarianceSkewNumerator beta n r <= 0 := by
  rw [oddPrismTransferBridgeVariance_eq_numerator_div beta n hn r,
    oddPrismTransferBridgeVariance_eq_numerator_div beta n hn (-r)]
  have hp := oddPrismTransferBridgeRawMoment_pos beta n hn r
  have hm := oddPrismTransferBridgeRawMoment_pos beta n hn (-r)
  rw [div_le_div_iff₀ (sq_pos_of_pos hp) (sq_pos_of_pos hm)]
  unfold oddPrismTransferBridgeVarianceSkewNumerator
  constructor <;> intro h <;> linarith


end
end StatMech.FrontierA
