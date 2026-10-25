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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part6
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


theorem rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tableCertifiedTotalBound = 2 := by
  norm_num [rawRowsZeroInfiniteTailPackage_replacedTailEnvelope,
    rawRowsZeroInfiniteTailPackage,
    ofExternalStableKeyRowsFiniteCutoffStableKey,
    tablePrefixBudget, tableFiniteBudget]


@[simp] theorem rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_certificate_eq
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).certificate =
      (rawRowsZeroInfiniteTailPackage (d := d) K).certificate :=
  rfl


theorem rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_tsum_le_two
    {d : ℕ} (K : TailCutoff)
    [DecidableEq (FiniteCutoffCoordinate d K)] :
    (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tailTotalTsum ≤ 2 := by
  rw [←
    rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
      (d := d) K]
  exact
    (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := d) K).tailTotalTsum_le_tableCertifiedTotalBound


end InfiniteTailStableKeyPackageExample
end Exact3D
end StatMech
