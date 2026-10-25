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
import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackageExample

theorem contributionSplitWitnessPackageCoarserTailEnvelope_totalBound_eq :
    contributionSplitWitnessPackageCoarserTailEnvelope.tailCertifiedTotalBound =
      (3 : ℝ) := by
  norm_num [contributionSplitWitnessPackageCoarserTailEnvelope,
    FiniteWitnessPackage.with_tailEnvelope_and_tailBudget,
    TailSummability.FiniteSupportCertificate.with_tailEnvelope_and_tailBound,
    FiniteWitnessPackage.tailCertifiedTotalBound,
    FiniteWitnessPackage.tailPrefixSum, FiniteWitnessPackage.tailBudget,
    contributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit]


theorem contributionSplitWitnessPackageCoarserTailEnvelope_certificate_eq :
    contributionSplitWitnessPackageCoarserTailEnvelope.certificate =
      contributionSplitWitnessPackage.certificate := by
  simp [contributionSplitWitnessPackageCoarserTailEnvelope]


theorem hierarchicalContributionSplitWitnessPackage_tail_bound_concrete :
    (∑' a, hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) ≤
      (11 : ℝ) / 5 := by
  have h := hierarchicalContributionSplitWitnessPackage.tail_tsum_le_prefix_add_tailBound
  norm_num [hierarchicalContributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit] at h ⊢


theorem hierarchicalContributionSplitWitnessPackage_tailCertifiedTotalBound_eq :
    hierarchicalContributionSplitWitnessPackage.tailCertifiedTotalBound =
      (11 : ℝ) / 5 := by
  norm_num [FiniteWitnessPackage.tailCertifiedTotalBound,
    FiniteWitnessPackage.tailPrefixSum, FiniteWitnessPackage.tailBudget,
    hierarchicalContributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit]


theorem hierarchicalContributionSplitWitnessPackage_tail_tsum_le_certifiedTotalBound :
    (∑' a, hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) ≤
      hierarchicalContributionSplitWitnessPackage.tailCertifiedTotalBound :=
  hierarchicalContributionSplitWitnessPackage.tail_tsum_le_certifiedTotalBound


theorem hierarchicalContributionSplitWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid correlationLength :=
  hierarchicalContributionSplitWitnessPackage.valid_of_bridge hbridge


theorem hierarchicalContributionSplitWitnessPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu HierarchicalModel correlationLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  hierarchicalContributionSplitWitnessPackage.hasCriticalNu_of_bridge hbridge


theorem
    hierarchicalContributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu HierarchicalModel correlationLength
        hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent) :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      correlationLength :=
  hierarchicalContributionSplitWitnessPackage.rgToExponentBridge_of_hasCriticalNu
    hν


theorem hierarchicalContributionSplitWitnessPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu HierarchicalModel correlationLength
        hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent) :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      correlationLength :=
  hierarchicalContributionSplitWitnessPackage.valid_of_hasCriticalNu hν

end FiniteWitnessPackageExample
end Exact3D
end StatMech
