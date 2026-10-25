/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilityExample
import Def.StatisticalMechanics.Code.Exact3D.ToyRG.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.Hierarchical.Part4
import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackageExample

theorem contributionSplitWitnessPackageRelaxedTailBudget_totalBound_eq :
    contributionSplitWitnessPackageRelaxedTailBudget.tailCertifiedTotalBound =
      (3 : ℝ) := by
  norm_num [contributionSplitWitnessPackageRelaxedTailBudget,
    FiniteWitnessPackage.with_larger_tailBudget,
    TailSummability.FiniteSupportCertificate.with_larger_tailBound,
    FiniteWitnessPackage.tailCertifiedTotalBound,
    FiniteWitnessPackage.tailPrefixSum, FiniteWitnessPackage.tailBudget,
    contributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn]


theorem contributionSplitWitnessPackage_tail_tsum_le_three :
    (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤
      (3 : ℝ) := by
  have h :=
    contributionSplitWitnessPackage.tail_tsum_le_prefix_add_of_tailBudget_le
      (tailBound' := (3 : ℝ))
      (by
        norm_num [FiniteWitnessPackage.tailBudget, contributionSplitWitnessPackage,
          FiniteWitnessPackage.ofContributionSplitFiniteSupport,
          ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn])
  have hprefix : contributionSplitWitnessPackage.tailPrefixSum = 0 := by
    norm_num [FiniteWitnessPackage.tailPrefixSum, contributionSplitWitnessPackage,
      FiniteWitnessPackage.ofContributionSplitFiniteSupport,
      ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
      TailSummabilityExample.exampleSplit]
  simpa [hprefix] using h


end FiniteWitnessPackageExample
end Exact3D
end StatMech
