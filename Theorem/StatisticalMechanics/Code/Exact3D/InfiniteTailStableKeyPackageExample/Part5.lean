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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tableCertifiedTotalBound =
      (support.card : ℝ) + 2 := by
  rw [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope]
  rw [with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound]
  change (support.card : ℝ) * (1 : ℝ) + 1 + 1 =
    (support.card : ℝ) + 2
  ring


theorem
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)]
    (support : Finset (FiniteCutoffCoordinate d K))
    (hsaturated :
      ∀ a,
        classifyFiniteCutoffMinimalCubicStableKey K a ∈
          support.image (classifyFiniteCutoffMinimalCubicStableKey K) →
        a ∈ support) :
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum ≤
      (support.card : ℝ) + 2 := by
  rw [←
    minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two
      K support hsaturated]
  exact
    (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope
      (d := d) K support hsaturated).tailTotalTsum_le_tableCertifiedTotalBound


theorem rawRowsZeroInfiniteTailPackage_relaxedTailBound_tailBound_eq_one
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    ((rawRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [rawRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffStableKey])).tailBound =
      1 :=
  rfl


theorem rawRowsZeroInfiniteTailPackage_relaxedTailBound_tailTotalTsum_le_one
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    ((rawRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [rawRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffStableKey])).tailTotalTsum
      ≤ 1 := by
  simpa [rawRowsZeroInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey, tableCertifiedTotalBound] using
    (((rawRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [rawRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffStableKey])).tailTotalTsum_le_tableCertifiedTotalBound)


theorem minimalCubicRowsZeroInfiniteTailPackage_relaxedTailBound_tailBound_eq_one
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    ((minimalCubicRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [minimalCubicRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).tailBound =
      1 :=
  rfl


theorem
    minimalCubicRowsZeroInfiniteTailPackage_relaxedTailBound_tailTotalTsum_le_one
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    ((minimalCubicRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [minimalCubicRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).tailTotalTsum
      ≤ 1 := by
  simpa [minimalCubicRowsZeroInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffMinimalCubic,
    tableCertifiedTotalBound] using
    (((minimalCubicRowsZeroInfiniteTailPackage
      (d := d) K).with_larger_tailBound
      (tailBound' := 1) (by
        norm_num [minimalCubicRowsZeroInfiniteTailPackage,
          ofExternalStableKeyRowsFiniteCutoffMinimalCubic]
      )).tailTotalTsum_le_tableCertifiedTotalBound)


end InfiniteTailStableKeyPackageExample
end Exact3D
end StatMech
