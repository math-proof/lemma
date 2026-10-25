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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part30


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem spin_ghsLAgreement
    {V : Type*} (s t : ConfigSpace V) (p : V) :
    spin (ghsLAgreement s t) p = spin s p * spin t p := by
  unfold ghsLAgreement spin
  cases hs : s p <;> cases ht : t p <;> norm_num [hs, ht]

theorem oddPrismLayerSeamInteraction_eq_agreementSpin
    (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerSeamInteraction n s t =
      oddPrismTransferAgreementSpin n (ghsLAgreement s t) := by
  unfold oddPrismLayerSeamInteraction oddPrismTransferAgreementSpin
  apply Finset.sum_congr rfl
  intro p _
  rw [spin_ghsLAgreement]

@[simp] theorem oddPrismLayerSeamInteraction_mate
    (n : Nat)
    (q s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerSeamInteraction n s (ghsLMate q s) =
      oddPrismTransferAgreementSpin n q := by
  rw [oddPrismLayerSeamInteraction_eq_agreementSpin,
    ghsLAgreement_mate]

theorem oddPrismTransferAgreementFibreMass_pos
    (beta : Real) (n : Nat)
    (q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    0 < oddPrismTransferAgreementFibreMass beta n q := by
  unfold oddPrismTransferAgreementFibreMass
  exact Finset.sum_pos (fun s _ => mul_pos
    (oddPrismLowerConditionedVector_pos beta n s)
    (oddPrismUpperConditionedVector_pos beta n (ghsLMate q s)))
    Finset.univ_nonempty


theorem oddPrismTransferBridgeRawMoment_eq_agreementTilt
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      ∑ q, oddPrismTransferAgreementFibreMass beta n q *
        Real.exp (r * oddPrismTransferAgreementSpin n q) := by
  unfold oddPrismTransferBridgeRawMoment
  rw [ghsL_sum_pair_xnor]
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferAgreementFibreMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  unfold oddPrismPureSeamKernel
  rw [oddPrismLayerSeamInteraction_mate]

theorem oddPrismTransferBridgeRawFirst_eq_agreementTilt
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawFirst beta n r =
      ∑ q, oddPrismTransferAgreementFibreMass beta n q *
        (oddPrismTransferAgreementSpin n q *
          Real.exp (r * oddPrismTransferAgreementSpin n q)) := by
  unfold oddPrismTransferBridgeRawFirst
  rw [ghsL_sum_pair_xnor]
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferAgreementFibreMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  unfold oddPrismPureSeamKernel
  rw [oddPrismLayerSeamInteraction_mate]

theorem oddPrismTransferBridgeRawSecond_eq_agreementTilt
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawSecond beta n r =
      ∑ q, oddPrismTransferAgreementFibreMass beta n q *
        (oddPrismTransferAgreementSpin n q ^ 2 *
          Real.exp (r * oddPrismTransferAgreementSpin n q)) := by
  unfold oddPrismTransferBridgeRawSecond
  rw [ghsL_sum_pair_xnor]
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferAgreementFibreMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  unfold oddPrismPureSeamKernel
  rw [oddPrismLayerSeamInteraction_mate]


end
end StatMech.FrontierA
