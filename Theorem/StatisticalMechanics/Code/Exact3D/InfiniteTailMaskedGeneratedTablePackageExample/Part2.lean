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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedGeneratedTablePackageExample

open BoundedPolymerCase

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailMaskedTableWitnessPackage


theorem generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  simp [generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope,
    generatedBoundedCaseMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofGeneratedIntervalTableFiniteCutoff,
    with_zero_tailEnvelope_and_budgets, with_tailEnvelope_and_budgets,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]

@[simp] theorem
    generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).certificate =
      (generatedBoundedCaseMaskedTablePackage
        (d := d) K support hsaturated).certificate :=
  rfl


theorem generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_tsum_le
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffCoordinate K a ∈
          support.image (classifyFiniteCutoffCoordinate K) →
        a ∈ support) :
    (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [← generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_budget_eq
    (d := d) K support hsaturated]
  exact
    (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


end InfiniteTailMaskedGeneratedTablePackageExample
end Exact3D
end StatMech
