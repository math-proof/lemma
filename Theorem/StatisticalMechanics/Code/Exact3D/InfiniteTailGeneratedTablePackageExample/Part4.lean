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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailGeneratedTablePackageExample.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailGeneratedTablePackageExample

open BoundedPolymerCase

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  rw [generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope]
  rw [with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound]
  change (support.card : ℝ) * (1 : ℝ) + 1 + 1 =
    (support.card : ℝ) + 2
  ring


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
      K support hsaturated]
  exact
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound

@[simp] theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate :=
  rfl


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hbridge :
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.RGToExponentBridge
        correlationLength := by
  simpa using hbridge


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_valid
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hvalid :
      (generatedMinimalCubicStableKeyInfiniteTailPackage
        (d := d) K support hsaturated).certificate.Valid
        correlationLength) :
    (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate.Valid
        correlationLength := by
  simpa using hvalid


theorem
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        (generatedMinimalCubicStableKeyInfiniteTailPackage
          (d := d) K support hsaturated).certificate.predictedExponent) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
        (d := d) K support hsaturated).certificate.predictedExponent := by
  simpa using hν


end InfiniteTailGeneratedTablePackageExample
end Exact3D
end StatMech
