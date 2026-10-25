/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailGeneratedTablePackage
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailGeneratedTablePackageExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailGeneratedTablePackageExample

open BoundedPolymerCase

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


theorem generatedBoundedCaseInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedCubicClassInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedStableKeyInfiniteTailPackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_finiteChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedBoundedCaseInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedBoundedCaseInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds


theorem generatedBoundedCaseInfiniteTailPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem generatedBoundedCaseInfiniteTailPackage_linearizationEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem generatedBoundedCaseInfiniteTailPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedBoundedCaseInfiniteTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry


theorem generatedCubicClassInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedCubicClassInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds


theorem generatedCubicClassInfiniteTailPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem generatedCubicClassInfiniteTailPackage_linearizationEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem generatedCubicClassInfiniteTailPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedCubicClassInfiniteTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry


theorem generatedStableKeyInfiniteTailPackage_finiteCaseChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedStableKeyInfiniteTailPackage_tailBounds {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds


theorem generatedStableKeyInfiniteTailPackage_fixedPointEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem generatedStableKeyInfiniteTailPackage_linearizationEnclosure {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem generatedStableKeyInfiniteTailPackage_hyperbolicSplitting {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedStableKeyInfiniteTailPackage_orbitEntry {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_finiteCaseChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FiniteCaseChecks :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).finiteCaseChecks


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_tailBounds
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.TailBounds :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).tailBounds


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_fixedPointEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.FixedPointEnclosure :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).fixedPointEnclosure


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_linearizationEnclosure
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.LinearizationEnclosure :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).linearizationEnclosure


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_hyperbolicSplitting
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.HyperbolicSplitting :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).hyperbolicSplitting


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_orbitEntry
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.OrbitEntry :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).orbitEntry


theorem generatedStableKeyInfiniteTailPackage_predictedExponent_eq_boundedCase
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hstable :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (hbounded :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hstable).certificate.predictedExponent =
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hbounded).certificate.predictedExponent := by
  rfl


theorem generatedBoundedCaseInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [generatedBoundedCaseInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]


theorem generatedCubicClassInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [generatedCubicClassInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedCubicIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]


theorem generatedStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [generatedStableKeyInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedStableKeyIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  simp [generatedMinimalCubicStableKeyInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound]


theorem generatedBoundedCaseInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [generatedBoundedCaseInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem generatedCubicClassInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [generatedCubicClassInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedCubicIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem generatedStableKeyInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [generatedStableKeyInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedStableKeyIntervalTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  simpa [generatedMinimalCubicStableKeyInfiniteTailPackage,
    InfiniteTailTableWitnessPackage.ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem generatedBoundedCaseInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem generatedBoundedCaseInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem generatedCubicClassInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem generatedCubicClassInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem generatedStableKeyInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem generatedStableKeyInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P :=
    generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P :=
    generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem generatedBoundedCaseInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    ((generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedBoundedCaseInfiniteTailPackage,
            ofGeneratedIntervalTableFiniteCutoff])).finiteBound =
      2 :=
  rfl


theorem generatedBoundedCaseInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    ((generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedBoundedCaseInfiniteTailPackage,
            ofGeneratedIntervalTableFiniteCutoff])).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [generatedBoundedCaseInfiniteTailPackage,
    ofGeneratedIntervalTableFiniteCutoff,
    with_larger_finiteBound, tableCertifiedTotalBound]


theorem generatedCubicClassInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    ((generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedCubicClassInfiniteTailPackage,
            ofGeneratedCubicIntervalTableFiniteCutoff])).finiteBound =
      2 :=
  rfl


theorem generatedCubicClassInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    ((generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedCubicClassInfiniteTailPackage,
            ofGeneratedCubicIntervalTableFiniteCutoff])).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [generatedCubicClassInfiniteTailPackage,
    ofGeneratedCubicIntervalTableFiniteCutoff,
    with_larger_finiteBound, tableCertifiedTotalBound]


theorem generatedStableKeyInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedStableKeyInfiniteTailPackage,
            ofGeneratedStableKeyIntervalTableFiniteCutoff])).finiteBound =
      2 :=
  rfl


theorem generatedStableKeyInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedStableKeyInfiniteTailPackage,
            ofGeneratedStableKeyIntervalTableFiniteCutoff])).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [generatedStableKeyInfiniteTailPackage,
    ofGeneratedStableKeyIntervalTableFiniteCutoff,
    with_larger_finiteBound, tableCertifiedTotalBound]


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedMinimalCubicStableKeyInfiniteTailPackage,
            ofGeneratedMinimalCubicStableKeyTableFiniteCutoff])).finiteBound =
      2 :=
  rfl


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [generatedMinimalCubicStableKeyInfiniteTailPackage,
            ofGeneratedMinimalCubicStableKeyTableFiniteCutoff]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [generatedMinimalCubicStableKeyInfiniteTailPackage,
    ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    with_larger_finiteBound, tableCertifiedTotalBound]


end InfiniteTailGeneratedTablePackageExample
end Exact3D
end StatMech
