/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackageExample

theorem geometricMaskedTableWitnessPackage_finiteChecks :
    geometricMaskedTableWitnessPackage.certificate.FiniteChecks :=
  geometricMaskedTableWitnessPackage.finiteChecks


theorem geometricMaskedTableWitnessPackage_tailBudget_eq_one :
    geometricMaskedTableWitnessPackage.tailBudget = 1 :=
  rfl


theorem geometricMaskedTableWitnessPackage_tableCertifiedTotalBound_eq_two :
    geometricMaskedTableWitnessPackage.tableCertifiedTotalBound = 2 := by
  norm_num [geometricMaskedTableWitnessPackage,
    InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound,
    InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget,
    InfiniteTailMaskedTableWitnessPackage.tableFiniteBudget]


theorem geometricMaskedTableWitnessPackage_tailTotalTsum_le_two :
    geometricMaskedTableWitnessPackage.tailTotalTsum ≤ 2 := by
  rw [← geometricMaskedTableWitnessPackage_tableCertifiedTotalBound_eq_two]
  exact
    geometricMaskedTableWitnessPackage.tailTotalTsum_le_tableCertifiedTotalBound


theorem geometricMaskedTableWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricMaskedTableWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    geometricMaskedTableWitnessPackage.certificate.Valid correlationLength :=
  geometricMaskedTableWitnessPackage.valid_of_bridge hbridge

end InfiniteTailMaskedTableWitnessPackageExample
end Exact3D
end StatMech
