/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackage
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part3
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


theorem rawRowsZeroInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.FiniteChecks :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).finiteChecks


theorem rawRowsZeroInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.FiniteCaseChecks :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).finiteCaseChecks


theorem rawRowsZeroInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.TailBounds :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).tailBounds


theorem rawRowsZeroInfiniteTailPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.FixedPointEnclosure :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).fixedPointEnclosure


theorem rawRowsZeroInfiniteTailPackage_linearizationEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.LinearizationEnclosure :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).linearizationEnclosure


theorem rawRowsZeroInfiniteTailPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.HyperbolicSplitting :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).hyperbolicSplitting


theorem rawRowsZeroInfiniteTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.OrbitEntry :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).orbitEntry


theorem minimalCubicRowsZeroInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.FiniteChecks :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).finiteChecks


theorem minimalCubicRowsZeroInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.FiniteCaseChecks :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).finiteCaseChecks


theorem minimalCubicRowsZeroInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.TailBounds :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tailBounds


theorem minimalCubicRowsZeroInfiniteTailPackage_fixedPointEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.FixedPointEnclosure :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).fixedPointEnclosure


theorem minimalCubicRowsZeroInfiniteTailPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.LinearizationEnclosure :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).linearizationEnclosure


theorem minimalCubicRowsZeroInfiniteTailPackage_hyperbolicSplitting
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.HyperbolicSplitting :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).hyperbolicSplitting


theorem minimalCubicRowsZeroInfiniteTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.OrbitEntry :=
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).orbitEntry


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_finiteChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_fixedPointEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_hyperbolicSplitting
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_orbitEntry
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_finiteCaseChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailBounds
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_fixedPointEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_hyperbolicSplitting
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_orbitEntry
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry


theorem rawRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).tableCertifiedTotalBound = 0 := by
  simp [rawRowsZeroInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]


theorem minimalCubicRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).tableCertifiedTotalBound = 0 := by
  simp [minimalCubicRowsZeroInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [rawZeroOneRowsIndicatorInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]


theorem rawRowsZeroInfiniteTailPackage_tailTotalTsum_le_zero {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum ≤ 0 := by
  simpa [rawRowsZeroInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (rawRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound


theorem minimalCubicRowsZeroInfiniteTailPackage_tailTotalTsum_le_zero {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum
      ≤ 0 := by
  simpa [minimalCubicRowsZeroInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [rawZeroOneRowsIndicatorInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey,
    tableCertifiedTotalBound] using
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    tableCertifiedTotalBound] using
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem rawRowsZeroInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).tailRemainderSum = 0 := by
  let P := rawRowsZeroInfiniteTailPackage (d := d) K
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem rawRowsZeroInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum =
      (rawRowsZeroInfiniteTailPackage (d := d) K).tailPrefixSum := by
  let P := rawRowsZeroInfiniteTailPackage (d := d) K
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem minimalCubicRowsZeroInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).tailRemainderSum = 0 := by
  let P := minimalCubicRowsZeroInfiniteTailPackage (d := d) K
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem minimalCubicRowsZeroInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum =
      (minimalCubicRowsZeroInfiniteTailPackage
        (d := d) K).tailPrefixSum := by
  let P := minimalCubicRowsZeroInfiniteTailPackage (d := d) K
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (rawZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P :=
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P :=
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [rawZeroOneRowsIndicatorInfiniteTailPackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey])).finiteBound =
      2 :=
  rfl


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [rawZeroOneRowsIndicatorInfiniteTailPackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [rawZeroOneRowsIndicatorInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey, with_larger_finiteBound,
    tableCertifiedTotalBound]


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).finiteBound =
      2 :=
  rfl


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic, with_larger_finiteBound,
    tableCertifiedTotalBound]


end InfiniteTailStableKeyPackageExample
end Exact3D
end StatMech
