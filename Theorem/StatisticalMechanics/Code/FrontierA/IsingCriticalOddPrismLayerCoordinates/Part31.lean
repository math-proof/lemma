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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part31


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismTransferAgreementTiltProb_pos
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    0 < oddPrismTransferAgreementTiltProb beta n r q := by
  unfold oddPrismTransferAgreementTiltProb
  exact div_pos (mul_pos
    (oddPrismTransferAgreementFibreMass_pos beta n q) (Real.exp_pos _))
    (oddPrismTransferBridgeRawMoment_pos beta n hn r)

theorem sum_oddPrismTransferAgreementTiltProb
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    (∑ q, oddPrismTransferAgreementTiltProb beta n r q) = 1 := by
  unfold oddPrismTransferAgreementTiltProb
  rw [← Finset.sum_div,
    ← oddPrismTransferBridgeRawMoment_eq_agreementTilt]
  exact div_self (oddPrismTransferBridgeRawMoment_pos beta n hn r).ne'

theorem oddPrismTransferAgreementSpin_monotone (n : Nat) :
    Monotone (oddPrismTransferAgreementSpin n) := by
  intro q s hqs
  unfold oddPrismTransferAgreementSpin
  exact Finset.sum_le_sum fun p _ => ifk_spin_mono hqs p

theorem oddPrismTransferAgreementTiltProb_mean
    (beta : Real) (n : Nat) (r : Real) :
    (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
      oddPrismTransferAgreementSpin n q) =
      oddPrismTransferBridgeRawFirst beta n r /
        oddPrismTransferBridgeRawMoment beta n r := by
  unfold oddPrismTransferAgreementTiltProb
  rw [show (∑ q, (oddPrismTransferAgreementFibreMass beta n q *
        Real.exp (r * oddPrismTransferAgreementSpin n q) /
          oddPrismTransferBridgeRawMoment beta n r) *
        oddPrismTransferAgreementSpin n q) =
      (∑ q, oddPrismTransferAgreementFibreMass beta n q *
        (oddPrismTransferAgreementSpin n q *
          Real.exp (r * oddPrismTransferAgreementSpin n q))) /
        oddPrismTransferBridgeRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _
    ring]
  rw [← oddPrismTransferBridgeRawFirst_eq_agreementTilt]

theorem oddPrismTransferAgreementTiltProb_second
    (beta : Real) (n : Nat) (r : Real) :
    (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
      oddPrismTransferAgreementSpin n q ^ 2) =
      oddPrismTransferBridgeRawSecond beta n r /
        oddPrismTransferBridgeRawMoment beta n r := by
  unfold oddPrismTransferAgreementTiltProb
  rw [show (∑ q, (oddPrismTransferAgreementFibreMass beta n q *
        Real.exp (r * oddPrismTransferAgreementSpin n q) /
          oddPrismTransferBridgeRawMoment beta n r) *
        oddPrismTransferAgreementSpin n q ^ 2) =
      (∑ q, oddPrismTransferAgreementFibreMass beta n q *
        (oddPrismTransferAgreementSpin n q ^ 2 *
          Real.exp (r * oddPrismTransferAgreementSpin n q))) /
        oddPrismTransferBridgeRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _
    ring]
  rw [← oddPrismTransferBridgeRawSecond_eq_agreementTilt]

theorem oddPrismTransferBridgeVariance_eq_agreementVariance
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n r =
      (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
        oddPrismTransferAgreementSpin n q ^ 2) -
      (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
        oddPrismTransferAgreementSpin n q) ^ 2 := by
  rw [oddPrismTransferAgreementTiltProb_mean,
    oddPrismTransferAgreementTiltProb_second]
  rfl


theorem oddPrismTransferBridgeVariance_le_neg_iff_agreementVariance
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n r <=
        oddPrismTransferBridgeVariance beta n (-r) ↔
      (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
          oddPrismTransferAgreementSpin n q ^ 2) -
        (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
          oddPrismTransferAgreementSpin n q) ^ 2 <=
      (∑ q, oddPrismTransferAgreementTiltProb beta n (-r) q *
          oddPrismTransferAgreementSpin n q ^ 2) -
        (∑ q, oddPrismTransferAgreementTiltProb beta n (-r) q *
          oddPrismTransferAgreementSpin n q) ^ 2 := by
  rw [oddPrismTransferBridgeVariance_eq_agreementVariance,
    oddPrismTransferBridgeVariance_eq_agreementVariance]


end
end StatMech.FrontierA
