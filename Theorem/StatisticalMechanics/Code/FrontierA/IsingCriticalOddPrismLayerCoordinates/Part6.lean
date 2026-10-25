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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part6


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

@[simp] theorem oddPrismLayerSeamInteraction_flip_right
    (n : Nat)
    (s q : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerSeamInteraction n s (FieldGhostDict.flipV q) =
      -oddPrismLayerSeamInteraction n s q := by
  unfold oddPrismLayerSeamInteraction
  simp_rw [FieldGhostDict.spin_flipV]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

@[simp] theorem oddPrismPureSeamKernel_flip_right
    (r : Real) (n : Nat)
    (s q : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismPureSeamKernel r n s (FieldGhostDict.flipV q) =
      oddPrismPureSeamKernel (-r) n s q := by
  unfold oddPrismPureSeamKernel
  rw [oddPrismLayerSeamInteraction_flip_right]
  congr 1
  ring


theorem oddPrismTransferBridgeRawMoment_neg_eq_flipped
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n (-r) =
      oddPrismTransferBridgeFlippedRawMoment beta n r := by
  unfold oddPrismTransferBridgeRawMoment
    oddPrismTransferBridgeFlippedRawMoment
  apply Finset.sum_congr rfl
  intro s _
  rw [← Equiv.sum_comp
    (FieldGhostDict.flipV_involutive
      (V := Fin (2 * n + 1) × Fin (2 * n + 1))).toPerm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Function.Involutive.coe_toPerm]
  rw [oddPrismPureSeamKernel_flip_right]
  simp [isingSumConfigEquiv, Equiv.sumPiEquivProdPi]

theorem oddPrismTransferBridgeRawFirst_neg_eq_neg_flipped
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawFirst beta n (-r) =
      -oddPrismTransferBridgeFlippedRawFirst beta n r := by
  unfold oddPrismTransferBridgeRawFirst
    oddPrismTransferBridgeFlippedRawFirst
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp
    (FieldGhostDict.flipV_involutive
      (V := Fin (2 * n + 1) × Fin (2 * n + 1))).toPerm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Function.Involutive.coe_toPerm]
  rw [oddPrismLayerSeamInteraction_flip_right,
    oddPrismPureSeamKernel_flip_right]
  simp only [neg_neg]
  ring

theorem oddPrismTransferBridgeRawSecond_neg_eq_flipped
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawSecond beta n (-r) =
      oddPrismTransferBridgeFlippedRawSecond beta n r := by
  unfold oddPrismTransferBridgeRawSecond
    oddPrismTransferBridgeFlippedRawSecond
  apply Finset.sum_congr rfl
  intro s _
  rw [← Equiv.sum_comp
    (FieldGhostDict.flipV_involutive
      (V := Fin (2 * n + 1) × Fin (2 * n + 1))).toPerm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Function.Involutive.coe_toPerm]
  rw [oddPrismLayerSeamInteraction_flip_right,
    oddPrismPureSeamKernel_flip_right]
  simp only [neg_neg]
  ring


theorem oddPrismTransferBridgeVariance_neg_eq_flipped
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n (-r) =
      oddPrismTransferBridgeFlippedVariance beta n r := by
  unfold oddPrismTransferBridgeVariance
    oddPrismTransferBridgeFlippedVariance
  rw [oddPrismTransferBridgeRawMoment_neg_eq_flipped,
    oddPrismTransferBridgeRawFirst_neg_eq_neg_flipped,
    oddPrismTransferBridgeRawSecond_neg_eq_flipped]
  ring


end
end StatMech.FrontierA
