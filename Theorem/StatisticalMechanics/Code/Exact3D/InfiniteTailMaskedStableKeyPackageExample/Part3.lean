/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedStableKeyPackage
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part3
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedStableKeyPackageExample.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailMaskedTableWitnessPackage


theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  simp [minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope,
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    with_zero_tailEnvelope_and_budgets, with_tailEnvelope_and_budgets,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]

@[simp] theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
        (d := d) K support hsaturated).certificate :=
  rfl


theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_tsum_le
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq
      (d := d) K support hsaturated]
  exact
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem rawRowsZeroMaskedTablePackage_tailTotalTsum_le_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroMaskedTablePackage (d := d) K).tailTotalTsum ≤ 0 := by
  rw [← rawRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero
    (d := d) K]
  exact
    (rawRowsZeroMaskedTablePackage
      (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound


theorem minimalCubicRowsZeroMaskedTablePackage_tailTotalTsum_le_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroMaskedTablePackage
      (d := d) K).tailTotalTsum ≤ 0 := by
  rw [← minimalCubicRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero
    (d := d) K]
  exact
    (minimalCubicRowsZeroMaskedTablePackage
      (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound


theorem rawZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← rawZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card
    (d := d) K support hsaturated]
  exact
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← minimalCubicZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card
    (d := d) K support hsaturated]
  exact
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem rawRowsZeroMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroMaskedTablePackage (d := d) K).tailRemainderSum = 0 := by
  let P := rawRowsZeroMaskedTablePackage (d := d) K
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem rawRowsZeroMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroMaskedTablePackage (d := d) K).tailTotalTsum =
      (rawRowsZeroMaskedTablePackage (d := d) K).tailPrefixSum := by
  let P := rawRowsZeroMaskedTablePackage (d := d) K
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem minimalCubicRowsZeroMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroMaskedTablePackage
      (d := d) K).tailRemainderSum = 0 := by
  let P := minimalCubicRowsZeroMaskedTablePackage (d := d) K
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem minimalCubicRowsZeroMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroMaskedTablePackage (d := d) K).tailTotalTsum =
      (minimalCubicRowsZeroMaskedTablePackage
        (d := d) K).tailPrefixSum := by
  let P := minimalCubicRowsZeroMaskedTablePackage (d := d) K
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem rawZeroOneRowsIndicatorMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := rawZeroOneRowsIndicatorMaskedTablePackage
    (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem rawZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (rawZeroOneRowsIndicatorMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := rawZeroOneRowsIndicatorMaskedTablePackage
    (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P :=
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P :=
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)

end InfiniteTailMaskedStableKeyPackageExample
end Exact3D
end StatMech
