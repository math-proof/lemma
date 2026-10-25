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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedStableKeyPackageExample.Part2
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
    rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  simp [rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope,
    rawZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey,
    with_zero_tailEnvelope_and_budgets, with_tailEnvelope_and_budgets,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]

@[simp] theorem
    rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (rawZeroOneRowsIndicatorMaskedTablePackage
        (d := d) K support hsaturated).certificate :=
  rfl


theorem
    rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_tsum_le
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [← rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq
    (d := d) K support hsaturated]
  exact
    (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


end InfiniteTailMaskedStableKeyPackageExample
end Exact3D
end StatMech
