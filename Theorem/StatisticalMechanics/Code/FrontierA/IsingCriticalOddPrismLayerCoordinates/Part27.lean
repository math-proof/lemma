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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part27


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismTransferBridgeFlippedRawMoment_pos
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    0 < oddPrismTransferBridgeFlippedRawMoment beta n r := by
  rw [← oddPrismTransferBridgeRawMoment_neg_eq_flipped]
  exact oddPrismTransferBridgeRawMoment_pos beta n hn (-r)

theorem sum_oddPrismTransferTiltedPairProb
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    (∑ x, oddPrismTransferTiltedPairProb beta n r x) = 1 := by
  unfold oddPrismTransferTiltedPairProb
  rw [← Finset.sum_div,
    ← oddPrismTransferBridgeRawMoment_eq_sum_tiltedPairWeight]
  exact div_self (oddPrismTransferBridgeRawMoment_pos beta n hn r).ne'

theorem sum_oddPrismTransferFlippedTiltedPairProb
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x) = 1 := by
  unfold oddPrismTransferFlippedTiltedPairProb
  rw [← Finset.sum_div,
    ← oddPrismTransferBridgeFlippedRawMoment_eq_sum_pairWeight]
  exact div_self (oddPrismTransferBridgeFlippedRawMoment_pos beta n hn r).ne'

theorem oddPrismTransferTiltedPairProb_nonneg
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    0 <= oddPrismTransferTiltedPairProb beta n r := by
  intro x
  exact div_nonneg (oddPrismTransferTiltedPairWeight_pos beta n r x).le
    (oddPrismTransferBridgeRawMoment_pos beta n hn r).le

theorem oddPrismTransferFlippedTiltedPairProb_nonneg
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    0 <= oddPrismTransferFlippedTiltedPairProb beta n r := by
  intro x
  exact div_nonneg (oddPrismTransferFlippedTiltedPairWeight_pos beta n r x).le
    (oddPrismTransferBridgeFlippedRawMoment_pos beta n hn r).le

theorem oddPrismTransferTiltedPairProb_flip_cross
    {beta r : Real} (hbeta : 0 <= beta) (hr : 0 <= r)
    (n : Nat) (hn : 0 < n)
    (x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTransferFlippedTiltedPairProb beta n r x *
        oddPrismTransferTiltedPairProb beta n r y <=
      oddPrismTransferFlippedTiltedPairProb beta n r (x ⊓ y) *
        oddPrismTransferTiltedPairProb beta n r (x ⊔ y) := by
  have hraw := oddPrismTransferTiltedPairWeight_flip_cross
    hbeta hr n hn x y
  unfold oddPrismTransferFlippedTiltedPairProb
    oddPrismTransferTiltedPairProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos
    (oddPrismTransferBridgeFlippedRawMoment_pos beta n hn r)
    (oddPrismTransferBridgeRawMoment_pos beta n hn r))).mpr hraw


theorem oddPrismTransferFlippedTiltedPair_le_of_monotone
    {beta r : Real} (hbeta : 0 <= beta) (hr : 0 <= r)
    (n : Nat) (hn : 0 < n)
    {g : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) -> Real}
    (hg : Monotone g) (hg0 : 0 <= g) :
    (∑ x, g x * oddPrismTransferFlippedTiltedPairProb beta n r x) <=
      ∑ x, g x * oddPrismTransferTiltedPairProb beta n r x := by
  apply holley
  · exact hg0
  · exact oddPrismTransferFlippedTiltedPairProb_nonneg beta n hn r
  · exact oddPrismTransferTiltedPairProb_nonneg beta n hn r
  · exact hg
  · rw [sum_oddPrismTransferFlippedTiltedPairProb beta n hn r,
      sum_oddPrismTransferTiltedPairProb beta n hn r]
  · exact oddPrismTransferTiltedPairProb_flip_cross hbeta hr n hn

theorem oddPrismTransferTiltedPairProb_mean
    (beta : Real) (n : Nat) (r : Real) :
    (∑ x, oddPrismTransferTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x) =
      oddPrismTransferBridgeRawFirst beta n r /
        oddPrismTransferBridgeRawMoment beta n r := by
  have hnum :
      (∑ x, oddPrismTransferTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x) =
        oddPrismTransferBridgeRawFirst beta n r := by
    unfold oddPrismTransferTiltedPairWeight oddPrismTransferPairBaseWeight
      oddPrismTransferPairInteraction oddPrismTransferBridgeRawFirst
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold oddPrismTransferTiltedPairProb
  rw [show (∑ x, oddPrismTransferTiltedPairWeight beta n r x /
      oddPrismTransferBridgeRawMoment beta n r *
        oddPrismTransferPairInteraction n x) =
      (∑ x, oddPrismTransferTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x) /
          oddPrismTransferBridgeRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [hnum]

theorem oddPrismTransferTiltedPairProb_second
    (beta : Real) (n : Nat) (r : Real) :
    (∑ x, oddPrismTransferTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x ^ 2) =
      oddPrismTransferBridgeRawSecond beta n r /
        oddPrismTransferBridgeRawMoment beta n r := by
  have hnum :
      (∑ x, oddPrismTransferTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) =
        oddPrismTransferBridgeRawSecond beta n r := by
    unfold oddPrismTransferTiltedPairWeight oddPrismTransferPairBaseWeight
      oddPrismTransferPairInteraction oddPrismTransferBridgeRawSecond
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold oddPrismTransferTiltedPairProb
  rw [show (∑ x, oddPrismTransferTiltedPairWeight beta n r x /
      oddPrismTransferBridgeRawMoment beta n r *
        oddPrismTransferPairInteraction n x ^ 2) =
      (∑ x, oddPrismTransferTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) /
          oddPrismTransferBridgeRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [hnum]

theorem oddPrismTransferBridgeVariance_eq_pairProbVariance
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n r =
      (∑ x, oddPrismTransferTiltedPairProb beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) -
      (∑ x, oddPrismTransferTiltedPairProb beta n r x *
        oddPrismTransferPairInteraction n x) ^ 2 := by
  rw [oddPrismTransferTiltedPairProb_mean,
    oddPrismTransferTiltedPairProb_second]
  rfl

theorem oddPrismTransferFlippedTiltedPairProb_mean
    (beta : Real) (n : Nat) (r : Real) :
    (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x) =
      oddPrismTransferBridgeFlippedRawFirst beta n r /
        oddPrismTransferBridgeFlippedRawMoment beta n r := by
  have hnum :
      (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x) =
        oddPrismTransferBridgeFlippedRawFirst beta n r := by
    unfold oddPrismTransferFlippedTiltedPairWeight
      oddPrismTransferPairInteraction oddPrismTransferBridgeFlippedRawFirst
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold oddPrismTransferFlippedTiltedPairProb
  rw [show (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x /
      oddPrismTransferBridgeFlippedRawMoment beta n r *
        oddPrismTransferPairInteraction n x) =
      (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x) /
          oddPrismTransferBridgeFlippedRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [hnum]

theorem oddPrismTransferFlippedTiltedPairProb_second
    (beta : Real) (n : Nat) (r : Real) :
    (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x ^ 2) =
      oddPrismTransferBridgeFlippedRawSecond beta n r /
        oddPrismTransferBridgeFlippedRawMoment beta n r := by
  have hnum :
      (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) =
        oddPrismTransferBridgeFlippedRawSecond beta n r := by
    unfold oddPrismTransferFlippedTiltedPairWeight
      oddPrismTransferPairInteraction oddPrismTransferBridgeFlippedRawSecond
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold oddPrismTransferFlippedTiltedPairProb
  rw [show (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x /
      oddPrismTransferBridgeFlippedRawMoment beta n r *
        oddPrismTransferPairInteraction n x ^ 2) =
      (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) /
          oddPrismTransferBridgeFlippedRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [hnum]

theorem oddPrismTransferBridgeFlippedVariance_eq_pairProbVariance
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeFlippedVariance beta n r =
      (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) -
      (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
        oddPrismTransferPairInteraction n x) ^ 2 := by
  rw [oddPrismTransferFlippedTiltedPairProb_mean,
    oddPrismTransferFlippedTiltedPairProb_second]
  rfl


theorem oddPrismTransferBridgeVariance_le_neg_iff_pairProbVariance
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n r <=
        oddPrismTransferBridgeVariance beta n (-r) ↔
      (∑ x, oddPrismTransferTiltedPairProb beta n r x *
          oddPrismTransferPairInteraction n x ^ 2) -
        (∑ x, oddPrismTransferTiltedPairProb beta n r x *
          oddPrismTransferPairInteraction n x) ^ 2 <=
      (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
          oddPrismTransferPairInteraction n x ^ 2) -
        (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
          oddPrismTransferPairInteraction n x) ^ 2 := by
  rw [oddPrismTransferBridgeVariance_neg_eq_flipped,
    oddPrismTransferBridgeVariance_eq_pairProbVariance,
    oddPrismTransferBridgeFlippedVariance_eq_pairProbVariance]


end
end StatMech.FrontierA
