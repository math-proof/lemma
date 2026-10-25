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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedStableKeyPackageExample
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


theorem rawRowsZeroMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroMaskedTablePackage (d := d) K).certificate.FiniteChecks :=
  (rawRowsZeroMaskedTablePackage (d := d) K).finiteChecks


theorem minimalCubicRowsZeroMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroMaskedTablePackage
      (d := d) K).certificate.FiniteChecks :=
  (minimalCubicRowsZeroMaskedTablePackage (d := d) K).finiteChecks


theorem rawZeroOneRowsIndicatorMaskedTablePackage_finiteChecks {d : ℕ}
    (K : TailCutoff) [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (rawZeroOneRowsIndicatorMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks


theorem minimalCubicZeroOneRowsIndicatorMaskedTablePackage_finiteChecks
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).certificate.FiniteChecks :=
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
    (d := d) K support hsaturated).finiteChecks


theorem rawRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroMaskedTablePackage
      (d := d) K).tableCertifiedTotalBound = 0 := by
  norm_num [rawRowsZeroMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]


theorem minimalCubicRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (minimalCubicRowsZeroMaskedTablePackage
      (d := d) K).tableCertifiedTotalBound = 0 := by
  norm_num [minimalCubicRowsZeroMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]


theorem rawZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    (rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [rawZeroOneRowsIndicatorMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffStableKey,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]


theorem minimalCubicZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) := by
  norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
    InfiniteTailMaskedTableWitnessPackage.ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]


theorem rawZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [rawZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey])).finiteBound =
      2 :=
  rfl


theorem rawZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [rawZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [rawZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey, with_larger_finiteBound,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]


theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).finiteBound =
      2 :=
  rfl


theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_budget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_finiteBound
        (finiteBound' := 2) (by
          norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) * 2 := by
  simp [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic, with_larger_finiteBound,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]


theorem rawZeroOneRowsIndicatorMaskedTablePackage_relaxedPrefixBudget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_prefixTailBound
        (prefixTailBound' := 1) (by
          norm_num [rawZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) + 1 := by
  simp [rawZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey, with_larger_prefixTailBound,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]


theorem
    minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedPrefixBudget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_prefixTailBound
        (prefixTailBound' := 1) (by
          norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) + 1 := by
  simp [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    with_larger_prefixTailBound, tableCertifiedTotalBound,
    tablePrefixBudget, tableFiniteBudget]


theorem rawZeroOneRowsIndicatorMaskedTablePackage_relaxedTailBudget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffStableKey K a ∈
          support.image (classifyFiniteCutoffStableKey K) →
        a ∈ support) :
    ((rawZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_tailBound
        (tailBound' := 1) (by
          norm_num [rawZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffStableKey]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) + 1 := by
  simp [rawZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey, with_larger_tailBound,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]


theorem minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedTailBudget_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage
      (d := d) K support hsaturated).with_larger_tailBound
        (tailBound' := 1) (by
          norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
            ofExternalStableKeyRowsFiniteCutoffMinimalCubic]
        )).tableCertifiedTotalBound =
      (support.card : ℝ) + 1 := by
  simp [minimalCubicZeroOneRowsIndicatorMaskedTablePackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic, with_larger_tailBound,
    tableCertifiedTotalBound, tablePrefixBudget, tableFiniteBudget]


end InfiniteTailMaskedStableKeyPackageExample
end Exact3D
end StatMech
