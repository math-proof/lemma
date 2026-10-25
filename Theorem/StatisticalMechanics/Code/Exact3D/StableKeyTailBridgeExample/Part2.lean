/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyTailBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificateExample.Part2
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyTailBridgeExample

theorem indicatorTailSplit_finiteContribution_eq_zero {d : ℕ}
    (K : TailCutoff) (support : Finset (FiniteCutoffCoordinate d K)) :
    ∀ c, (indicatorTailSplit (d := d) K support).finiteContribution c = 0 := by
  intro _
  rfl

@[simp] theorem singletonEmptySupport_card {d : ℕ} (K : TailCutoff) :
    (singletonEmptySupport (d := d) K).card = 1 := by
  simp [singletonEmptySupport]

@[simp] theorem indicatorTailSplit_total_emptyFiniteCutoffCoordinate {d : ℕ}
    (K : TailCutoff) :
    (indicatorTailSplit (d := d) K (singletonEmptySupport (d := d) K)).totalContribution
      (emptyFiniteCutoffCoordinate d K) = (1 : ℝ) / 10 := by
  simp [indicatorTailSplit, singletonEmptySupport]


theorem indicatorTailSplit_additive {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (indicatorTailSplit (d := d) K support).Additive := by
  intro a
  by_cases ha : a ∈ support <;> simp [indicatorTailSplit, ha]


theorem indicatorTailSplit_total_zero_off_support {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    ∀ a, a ∉ support →
      (indicatorTailSplit (d := d) K support).totalContribution a = 0 := by
  intro a ha
  simp [indicatorTailSplit, ha]


theorem indicatorTailSplit_tailEnvelopeOn {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (indicatorTailSplit (d := d) K support).TailEnvelopeOn support
      (fun _ => (1 : ℝ) / 10) := by
  intro a ha
  simp [indicatorTailSplit, ha]


theorem indicatorTailSplit_total_nonneg {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    ∀ a, 0 ≤ (indicatorTailSplit (d := d) K support).totalContribution a := by
  intro a
  by_cases ha : a ∈ support
  · simp [indicatorTailSplit, ha]
  · simp [indicatorTailSplit, ha]


theorem indicatorTailSplit_tailEnvelope_sum_le {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (∑ _a ∈ support, ((1 : ℝ) / 10)) ≤
      (support.card : ℝ) * ((1 : ℝ) / 10) := by
  simp [Finset.sum_const, nsmul_eq_mul]


theorem rawRows_row_upper_zero (d R maxDegree maxRange : ℕ)
    (row : StableKeyIntervalRow maxDegree maxRange)
    (hrow : row ∈ StableKeyCertificateExample.rawRows d R maxDegree maxRange) :
    ((row.interval.upper : ℚ) : ℝ) ≤ 0 := by
  exact StableKeyIntervalRow.upper_le_of_mem_rowsOfKeys
    ((exhaustiveTable d R maxDegree maxRange).image stableKey)
    (fun _ => StableKeyCertificateExample.zeroInterval)
    (fun _ _ => by
      norm_num [StableKeyCertificateExample.zeroInterval,
        RatInterval.point])
    (by simpa [StableKeyCertificateExample.rawRows] using hrow)


theorem rawRows_row_upper_one (d R maxDegree maxRange : ℕ)
    (row : StableKeyIntervalRow maxDegree maxRange)
    (hrow : row ∈ StableKeyCertificateExample.rawRows d R maxDegree maxRange) :
    ((row.interval.upper : ℚ) : ℝ) ≤ 1 :=
  le_trans (rawRows_row_upper_zero d R maxDegree maxRange row hrow) (by norm_num)


theorem minimalCubicRows_row_upper_zero (d R maxDegree maxRange : ℕ)
    (row : StableKeyIntervalRow maxDegree maxRange)
    (hrow : row ∈ StableKeyCertificateExample.minimalCubicRows d R maxDegree maxRange) :
    ((row.interval.upper : ℚ) : ℝ) ≤ 0 := by
  exact StableKeyIntervalRow.upper_le_of_mem_rowsOfKeys
    ((exhaustiveCubicClassTable d R maxDegree maxRange).image
      minimalCubicStableKey)
    (fun _ => StableKeyCertificateExample.zeroInterval)
    (fun _ _ => by
      norm_num [StableKeyCertificateExample.zeroInterval,
        RatInterval.point])
    (by simpa [StableKeyCertificateExample.minimalCubicRows] using hrow)


theorem minimalCubicRows_row_upper_one (d R maxDegree maxRange : ℕ)
    (row : StableKeyIntervalRow maxDegree maxRange)
    (hrow : row ∈ StableKeyCertificateExample.minimalCubicRows d R maxDegree maxRange) :
    ((row.interval.upper : ℚ) : ℝ) ≤ 1 :=
  le_trans (minimalCubicRows_row_upper_zero d R maxDegree maxRange row hrow) (by norm_num)


theorem rawRows_zero_finiteTableUpperBound_exactKeySet {d : ℕ}
    (K : TailCutoff) :
    FiniteTableUpperBound
      (externalStableKeyIntervalRowTable
        (StableKeyCertificateExample.rawRows
          d K.radius K.maxDegree K.maxRange)
        StableKeyCertificateExample.zeroInterval)
      (classifyFiniteCutoffStableKey (d := d) K)
      (fun _ : FiniteCutoffCoordinate d K => (0 : ℝ)) 0 := by
  exact externalStableKeyIntervalRowTable_finiteTableUpperBound_of_exactKeySet
    (StableKeyCertificateExample.rawRows
      d K.radius K.maxDegree K.maxRange)
    StableKeyCertificateExample.zeroInterval
    ((exhaustiveTable d K.radius K.maxDegree K.maxRange).image stableKey)
    (classifyFiniteCutoffStableKey (d := d) K)
    (fun _ : FiniteCutoffCoordinate d K => (0 : ℝ))
    (fun _ => (0 : ℝ))
    (StableKeyCertificateExample.rawRows_exactKeySet
      d K.radius K.maxDegree K.maxRange)
    (fun c =>
      Finset.mem_image.mpr
        ⟨classifyFiniteCutoffCoordinate K c,
          exhaustiveTable_covers d K.radius K.maxDegree K.maxRange
            (classifyFiniteCutoffCoordinate K c),
          rfl⟩)
    (fun _ => rfl)
    (StableKeyCertificateExample.rawRows_row_sound
      d K.radius K.maxDegree K.maxRange)
    (rawRows_row_upper_zero d K.radius K.maxDegree K.maxRange)


theorem rawRows_zero_tsum_total_le {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (∑' a, (zeroSplit (d := d) K).totalContribution a) ≤
      (support.card : ℝ) * 0 + 0 := by
  exact tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffStableKey
    K (zeroSplit (d := d) K)
    (StableKeyCertificateExample.rawRows d K.radius K.maxDegree K.maxRange)
    StableKeyCertificateExample.zeroInterval (fun _ => (0 : ℝ)) support (fun _ => (0 : ℝ))
    (zeroSplit_total_zero_off_support K support)
    (zeroSplit_additive K)
    (StableKeyCertificateExample.rawRows_cover d K.radius K.maxDegree K.maxRange)
    (fun _ => rfl)
    (StableKeyCertificateExample.rawRows_row_sound d K.radius K.maxDegree K.maxRange)
    (rawRows_row_upper_zero d K.radius K.maxDegree K.maxRange)
    (zeroSplit_tailEnvelopeOn K support)
    (zero_tailEnvelope_sum_le K support)


theorem minimalCubicRows_zero_tsum_total_le {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (∑' a, (zeroSplit (d := d) K).totalContribution a) ≤
      (support.card : ℝ) * 0 + 0 := by
  exact tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic
    K (zeroSplit (d := d) K)
    (StableKeyCertificateExample.minimalCubicRows d K.radius K.maxDegree K.maxRange)
    StableKeyCertificateExample.zeroInterval (fun _ => (0 : ℝ)) support (fun _ => (0 : ℝ))
    (zeroSplit_total_zero_off_support K support)
    (zeroSplit_additive K)
    (StableKeyCertificateExample.minimalCubicRows_cover d K.radius K.maxDegree K.maxRange)
    (fun _ => rfl)
    (StableKeyCertificateExample.minimalCubicRows_row_sound d K.radius K.maxDegree K.maxRange)
    (minimalCubicRows_row_upper_zero d K.radius K.maxDegree K.maxRange)
    (zeroSplit_tailEnvelopeOn K support)
    (zero_tailEnvelope_sum_le K support)


theorem rawRows_indicatorTail_tsum_total_le {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (∑' a, (indicatorTailSplit (d := d) K support).totalContribution a) ≤
      (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
  exact tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffStableKey
    K (indicatorTailSplit (d := d) K support)
    (StableKeyCertificateExample.rawRows d K.radius K.maxDegree K.maxRange)
    StableKeyCertificateExample.zeroInterval (fun _ => (0 : ℝ)) support
    (fun _ => (1 : ℝ) / 10)
    (indicatorTailSplit_total_zero_off_support K support)
    (indicatorTailSplit_additive K support)
    (StableKeyCertificateExample.rawRows_cover d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_finiteContribution_eq_zero K support)
    (StableKeyCertificateExample.rawRows_row_sound d K.radius K.maxDegree K.maxRange)
    (rawRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_tailEnvelopeOn K support)
    (indicatorTailSplit_tailEnvelope_sum_le K support)


theorem minimalCubicRows_indicatorTail_tsum_total_le {d : ℕ}
    (K : TailCutoff) (support : Finset (FiniteCutoffCoordinate d K)) :
    (∑' a, (indicatorTailSplit (d := d) K support).totalContribution a) ≤
      (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
  exact tsum_total_le_of_externalStableKeyIntervalRows_finiteCutoffMinimalCubic
    K (indicatorTailSplit (d := d) K support)
    (StableKeyCertificateExample.minimalCubicRows d K.radius K.maxDegree K.maxRange)
    StableKeyCertificateExample.zeroInterval (fun _ => (0 : ℝ)) support
    (fun _ => (1 : ℝ) / 10)
    (indicatorTailSplit_total_zero_off_support K support)
    (indicatorTailSplit_additive K support)
    (StableKeyCertificateExample.minimalCubicRows_cover d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_finiteContribution_eq_zero K support)
    (StableKeyCertificateExample.minimalCubicRows_row_sound d K.radius K.maxDegree K.maxRange)
    (minimalCubicRows_row_upper_one d K.radius K.maxDegree K.maxRange)
    (indicatorTailSplit_tailEnvelopeOn K support)
    (indicatorTailSplit_tailEnvelope_sum_le K support)


theorem rawRows_singletonIndicatorTail_tsum_total_le {d : ℕ} (K : TailCutoff) :
    (∑' a,
        (indicatorTailSplit (d := d) K
          (singletonEmptySupport (d := d) K)).totalContribution a) ≤
      (1 : ℝ) + (1 : ℝ) / 10 := by
  simpa [singletonEmptySupport] using
    rawRows_indicatorTail_tsum_total_le (d := d) K
      (singletonEmptySupport (d := d) K)


theorem minimalCubicRows_singletonIndicatorTail_tsum_total_le {d : ℕ}
    (K : TailCutoff) :
    (∑' a,
        (indicatorTailSplit (d := d) K
          (singletonEmptySupport (d := d) K)).totalContribution a) ≤
      (1 : ℝ) + (1 : ℝ) / 10 := by
  simpa [singletonEmptySupport] using
    minimalCubicRows_indicatorTail_tsum_total_le (d := d) K
      (singletonEmptySupport (d := d) K)


end StableKeyTailBridgeExample
end BoundedPolymerCase
end Exact3D
end StatMech
