/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
import Def.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCriticalCutHorizontalCrossingSourceExpectation_eq_sum
    (R : FKRectTorus) (q : Real) :
    fkRectCriticalCutHorizontalCrossingSourceExpectation R q =
      ∑ y : Fin R.height,
        fkRectCriticalCutHorizontalCrossingSourceMass R q y := by
  classical
  unfold fkRectCriticalCutHorizontalCrossingSourceExpectation
    fkRectCriticalCutHorizontalCrossingSourceMass
    fkRectCutHorizontalCrossingSourceCount
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          ↑((Finset.univ.filter fun y : Fin R.height =>
            FKRectCutHorizontalCrossingSource R omega y).card)) =
        ∑ omega : R.Configuration, ∑ y : Fin R.height,
          if FKRectCutHorizontalCrossingSource R omega y then
            fkRectCriticalRandomClusterProb R q omega else 0 := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hcross : FKRectCutHorizontalCrossingSource R omega y
      · simp [hcross]
      · simp [hcross]
    _ = ∑ y : Fin R.height, ∑ omega : R.Configuration,
          if FKRectCutHorizontalCrossingSource R omega y then
            fkRectCriticalRandomClusterProb R q omega else 0 := by
      rw [Finset.sum_comm]

theorem fkRectCriticalCutHorizontalCrossingSourceExpectation_le_height
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    fkRectCriticalCutHorizontalCrossingSourceExpectation R q ≤ R.height := by
  unfold fkRectCriticalCutHorizontalCrossingSourceExpectation
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectCutHorizontalCrossingSourceCount R omega) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega * R.height := by
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast
          fkRectCutHorizontalCrossingSourceCount_le_height R omega)
        (fkRectCriticalRandomClusterProb_nonneg R hq omega)
    _ = R.height := by
      rw [← Finset.sum_mul, sum_fkRectCriticalRandomClusterProb R hq,
        one_mul]

theorem fkRectCriticalCutHorizontalCrossingClusterExpectation_le_source
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    fkRectCriticalCutHorizontalCrossingClusterExpectation R q ≤
      fkRectCriticalCutHorizontalCrossingSourceExpectation R q := by
  unfold fkRectCriticalCutHorizontalCrossingClusterExpectation
    fkRectCriticalCutHorizontalCrossingSourceExpectation
  apply Finset.sum_le_sum
  intro omega homega
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast
      fkRectCutHorizontalCrossingClusterCount_le_sourceCount R omega)
    (fkRectCriticalRandomClusterProb_nonneg R hq omega)


theorem fkRectCriticalZeroTurnExpectation_le_two_width_add_cutCrossing
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (hcut : ∀ omega : R.Configuration,
      fkRectZeroTurnLoopCount R omega ≤
        2 * R.width + fkRectCutHorizontalCrossingSourceCount R omega) :
    fkRectCriticalZeroTurnExpectation R q ≤
      2 * R.width +
        fkRectCriticalCutHorizontalCrossingSourceExpectation R q := by
  unfold fkRectCriticalZeroTurnExpectation
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectZeroTurnLoopCount R omega) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega *
            (2 * R.width +
              fkRectCutHorizontalCrossingSourceCount R omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast hcut omega)
        (fkRectCriticalRandomClusterProb_nonneg R hq omega)
    _ = 2 * R.width +
        fkRectCriticalCutHorizontalCrossingSourceExpectation R q := by
      unfold fkRectCriticalCutHorizontalCrossingSourceExpectation
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_fkRectCriticalRandomClusterProb R hq, one_mul]


theorem fkRectCriticalZeroTurnExpectation_le_two_width_add_cutClusters
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (hcut : ∀ omega : R.Configuration,
      fkRectZeroTurnLoopCount R omega ≤
        2 * R.width + fkRectCutHorizontalCrossingClusterCount R omega) :
    fkRectCriticalZeroTurnExpectation R q ≤
      2 * R.width +
        fkRectCriticalCutHorizontalCrossingClusterExpectation R q := by
  unfold fkRectCriticalZeroTurnExpectation
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectZeroTurnLoopCount R omega) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega *
            (2 * R.width +
              fkRectCutHorizontalCrossingClusterCount R omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast hcut omega)
        (fkRectCriticalRandomClusterProb_nonneg R hq omega)
    _ = 2 * R.width +
        fkRectCriticalCutHorizontalCrossingClusterExpectation R q := by
      unfold fkRectCriticalCutHorizontalCrossingClusterExpectation
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_fkRectCriticalRandomClusterProb R hq, one_mul]

end
end StatMech.FrontierD
