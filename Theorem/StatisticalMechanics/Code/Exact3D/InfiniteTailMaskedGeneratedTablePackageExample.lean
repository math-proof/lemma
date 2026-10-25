/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedGeneratedTablePackage
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedGeneratedTablePackageExample

open BoundedPolymerCase

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailMaskedTableWitnessPackage


theorem generatedBoundedCaseMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedBoundedCaseMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedCubicClassMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedCubicClassMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedStableKeyMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedStableKeyMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedMinimalCubicStableKeyMaskedTablePackage_finiteChecks
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (generatedMinimalCubicStableKeyMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks


theorem generatedBoundedCaseMaskedTablePackage_budget_eq_card {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [generatedBoundedCaseMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofGeneratedIntervalTableFiniteCutoff,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]


theorem generatedBoundedCaseMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedBoundedCaseMaskedTablePackage_budget_eq_card]
  exact
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem generatedCubicClassMaskedTablePackage_budget_eq_card {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [generatedCubicClassMaskedTablePackage,
    ofGeneratedCubicIntervalTableFiniteCutoff,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]


theorem generatedCubicClassMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedCubicClassMaskedTablePackage_budget_eq_card]
  exact
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem generatedStableKeyMaskedTablePackage_budget_eq_card {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [generatedStableKeyMaskedTablePackage,
    ofGeneratedStableKeyIntervalTableFiniteCutoff,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]


theorem generatedStableKeyMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedStableKeyMaskedTablePackage_budget_eq_card]
  exact
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem generatedMinimalCubicStableKeyMaskedTablePackage_budget_eq_card
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [generatedMinimalCubicStableKeyMaskedTablePackage,
    ofGeneratedMinimalCubicStableKeyTableFiniteCutoff,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]


theorem generatedMinimalCubicStableKeyMaskedTablePackage_tailTotalTsum_le_card
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) := by
  rw [← generatedMinimalCubicStableKeyMaskedTablePackage_budget_eq_card]
  exact
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem generatedBoundedCaseMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem generatedBoundedCaseMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedBoundedCaseMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem generatedCubicClassMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedCubicClassMaskedTablePackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem generatedCubicClassMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCubicClass K a ∈
          support.image (classifyFiniteCutoffCubicClass K) →
        a ∈ support) :
    (generatedCubicClassMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedCubicClassMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedCubicClassMaskedTablePackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem generatedStableKeyMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P := generatedStableKeyMaskedTablePackage (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem generatedStableKeyMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (generatedStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedStableKeyMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P := generatedStableKeyMaskedTablePackage (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


theorem
    generatedMinimalCubicStableKeyMaskedTablePackage_tailRemainderSum_eq_zero
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailRemainderSum = 0 := by
  let P :=
    generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated
  exact P.tailRemainderSum_eq_zero_of_tailBudget_eq_zero (by rfl)


theorem
    generatedMinimalCubicStableKeyMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum
    {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated).tailTotalTsum =
      (generatedMinimalCubicStableKeyMaskedTablePackage
        (d := d) K support hsaturated).tailPrefixSum := by
  let P :=
    generatedMinimalCubicStableKeyMaskedTablePackage
      (d := d) K support hsaturated
  exact P.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero (by rfl)


end InfiniteTailMaskedGeneratedTablePackageExample
end Exact3D
end StatMech
