/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackageExample

theorem geometricContributionSplitMaskedTailEnvelopeWitnessPackage_finiteChecks :
    RGCertificate.FiniteChecks
      geometricContributionSplitMaskedTailEnvelopeWitnessPackage.certificate :=
  geometricContributionSplitMaskedTailEnvelopeWitnessPackage.finiteChecks


theorem
    geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailBudget_eq_one :
    geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailBudget = 1 :=
  rfl


theorem
    geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailTotalTsum_le_prefix_add_one :
    geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailTotalTsum ≤
      geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailPrefixSum +
        1 := by
  have hbudget :
      geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailBudget ≤
        1 := by
    rw
      [geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailBudget_eq_one]
  exact
    InfiniteTailWitnessPackage.tailTotalTsum_le_prefix_add_of_tailBudget_le
      geometricContributionSplitMaskedTailEnvelopeWitnessPackage hbudget


end InfiniteTailWitnessPackageExample
end Exact3D
end StatMech
