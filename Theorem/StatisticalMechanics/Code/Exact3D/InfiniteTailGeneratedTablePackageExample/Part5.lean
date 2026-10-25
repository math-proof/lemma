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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailGeneratedTablePackageExample.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailGeneratedTablePackageExample

open BoundedPolymerCase

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


theorem
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  rw [generatedStableKeyInfiniteTailPackage_replacedTailEnvelope]
  rw [with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound]
  change (support.card : ℝ) * (1 : ℝ) + 1 + 1 =
    (support.card : ℝ) + 2
  ring


theorem generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
      K support hsaturated]
  exact
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound

@[simp] theorem
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate :=
  rfl


theorem
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hbridge :
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge


theorem generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_valid
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hvalid :
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.Valid
        correlationLength) :
    (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.Valid
        correlationLength := by
  simpa using hvalid


theorem
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
        (d := d) K support hsaturated).certificate.predictedExponent := by
  simpa using hν


theorem generatedBoundedCaseInfiniteTailPackage_rgToExponentBridge_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  hbridge


theorem generatedCubicClassInfiniteTailPackage_rgToExponentBridge_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  hbridge


theorem generatedStableKeyInfiniteTailPackage_rgToExponentBridge_of_bridge
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
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  hbridge


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_rgToExponentBridge_of_bridge
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
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  hbridge


theorem generatedBoundedCaseInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge


theorem generatedBoundedCaseInfiniteTailPackage_hasCriticalNu_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedBoundedCaseInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge


theorem generatedCubicClassInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge


theorem generatedCubicClassInfiniteTailPackage_hasCriticalNu_of_bridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedCubicClassInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge


theorem generatedStableKeyInfiniteTailPackage_valid_of_bridge {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge


theorem generatedStableKeyInfiniteTailPackage_hasCriticalNu_of_bridge
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
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_valid_of_bridge
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
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid
      correlationLength :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_bridge hbridge


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_hasCriticalNu_of_bridge
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
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.predictedExponent :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).hasCriticalNu_of_bridge hbridge


theorem generatedBoundedCaseInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedBoundedCaseInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν


theorem generatedBoundedCaseInfiniteTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedBoundedCaseInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedBoundedCaseInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedBoundedCaseInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν


theorem generatedCubicClassInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedCubicClassInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν


theorem generatedCubicClassInfiniteTailPackage_valid_of_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedCubicClassInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedCubicClassInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedCubicClassInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν


theorem generatedStableKeyInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
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
        (generatedStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν


theorem generatedStableKeyInfiniteTailPackage_valid_of_hasCriticalNu
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
        (generatedStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
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
        (generatedMinimalCubicStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.RGToExponentBridge
      correlationLength :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).rgToExponentBridge_of_hasCriticalNu hν


theorem generatedMinimalCubicStableKeyInfiniteTailPackage_valid_of_hasCriticalNu
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
        (generatedMinimalCubicStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage
      (d := d) K support hsaturated).certificate.Valid correlationLength :=
  (generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := d) K support hsaturated).valid_of_hasCriticalNu hν

end InfiniteTailGeneratedTablePackageExample
end Exact3D
end StatMech
