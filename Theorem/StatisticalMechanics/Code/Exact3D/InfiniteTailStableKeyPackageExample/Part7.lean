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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part7
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


theorem minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tableCertifiedTotalBound = 2 := by
  norm_num [minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope,
    minimalCubicRowsZeroInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    tablePrefixBudget, tableFiniteBudget]


@[simp] theorem
    minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).certificate =
      (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate :=
  rfl


theorem minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_tsum_le_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tailTotalTsum ≤ 2 := by
  rw [←
    minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
      (d := d) K]
  exact
    (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound


theorem rawRowsZeroInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (rawRowsZeroInfiniteTailPackage
        (d := d) K).certificate.RGToExponentBridge correlationLength) :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.Valid correlationLength :=
  (rawRowsZeroInfiniteTailPackage (d := d) K).valid_of_bridge hbridge


theorem rawRowsZeroInfiniteTailPackage_hasCriticalNu_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (rawRowsZeroInfiniteTailPackage
        (d := d) K).certificate.RGToExponentBridge correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (rawRowsZeroInfiniteTailPackage
        (d := d) K).certificate.predictedExponent :=
  (rawRowsZeroInfiniteTailPackage
    (d := d) K).hasCriticalNu_of_bridge hbridge


theorem minimalCubicRowsZeroInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (minimalCubicRowsZeroInfiniteTailPackage
        (d := d) K).certificate.RGToExponentBridge correlationLength) :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.Valid correlationLength :=
  (minimalCubicRowsZeroInfiniteTailPackage
    (d := d) K).valid_of_bridge hbridge


theorem minimalCubicRowsZeroInfiniteTailPackage_hasCriticalNu_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (minimalCubicRowsZeroInfiniteTailPackage
        (d := d) K).certificate.RGToExponentBridge correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (minimalCubicRowsZeroInfiniteTailPackage
        (d := d) K).certificate.predictedExponent :=
  (minimalCubicRowsZeroInfiniteTailPackage
    (d := d) K).hasCriticalNu_of_bridge hbridge


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (rawZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_hasCriticalNu_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (rawZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (rawZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_valid_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_hasCriticalNu_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge


theorem rawRowsZeroInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (rawRowsZeroInfiniteTailPackage
          (d := d) K).certificate.predictedExponent) :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.RGToExponentBridge correlationLength :=
  (rawRowsZeroInfiniteTailPackage
    (d := d) K).rgToExponentBridge_of_hasCriticalNu hν


theorem rawRowsZeroInfiniteTailPackage_valid_of_hasCriticalNu {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (rawRowsZeroInfiniteTailPackage
          (d := d) K).certificate.predictedExponent) :
    (rawRowsZeroInfiniteTailPackage
      (d := d) K).certificate.Valid correlationLength :=
  (rawRowsZeroInfiniteTailPackage
    (d := d) K).valid_of_hasCriticalNu hν


theorem
    minimalCubicRowsZeroInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (minimalCubicRowsZeroInfiniteTailPackage
          (d := d) K).certificate.predictedExponent) :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.RGToExponentBridge correlationLength :=
  (minimalCubicRowsZeroInfiniteTailPackage
    (d := d) K).rgToExponentBridge_of_hasCriticalNu hν


theorem minimalCubicRowsZeroInfiniteTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (minimalCubicRowsZeroInfiniteTailPackage
          (d := d) K).certificate.predictedExponent) :
    (minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).certificate.Valid correlationLength :=
  (minimalCubicRowsZeroInfiniteTailPackage
    (d := d) K).valid_of_hasCriticalNu hν


theorem
    rawZeroOneRowsIndicatorInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (rawZeroOneRowsIndicatorInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν


theorem rawZeroOneRowsIndicatorInfiniteTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (rawZeroOneRowsIndicatorInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (rawZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (rawZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν

end InfiniteTailStableKeyPackageExample
end Exact3D
end StatMech
