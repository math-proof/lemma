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
import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackageExample

theorem hierarchicalContributionSplitWitnessPackage_fixedPoint_eq :
    hierarchicalContributionSplitWitnessPackage.rgMap.map
      hierarchicalContributionSplitWitnessPackage.fixedPoint =
    hierarchicalContributionSplitWitnessPackage.fixedPoint :=
  hierarchicalContributionSplitWitnessPackage.fixedPoint_eq


theorem hierarchicalContributionSplitWitnessPackage_stable_unique :
    ∃! p : Fin 1 → ℝ, hierarchicalStableWitness.map p = p :=
  hierarchicalStableWitness.exists_unique_fixedPoint


theorem hierarchicalContributionSplitWitnessPackage_finiteChecks :
    hierarchicalContributionSplitWitnessPackage.certificate.FiniteChecks :=
  hierarchicalContributionSplitWitnessPackage.finiteChecks


theorem hierarchicalContributionSplitWitnessPackage_finiteCaseChecks :
    hierarchicalContributionSplitWitnessPackage.certificate.FiniteCaseChecks :=
  hierarchicalContributionSplitWitnessPackage.finiteCaseChecks


theorem hierarchicalContributionSplitWitnessPackage_tailBounds :
    hierarchicalContributionSplitWitnessPackage.certificate.TailBounds :=
  hierarchicalContributionSplitWitnessPackage.tailBounds


theorem hierarchicalContributionSplitWitnessPackage_fixedPointEnclosure :
    hierarchicalContributionSplitWitnessPackage.certificate.FixedPointEnclosure :=
  hierarchicalContributionSplitWitnessPackage.fixedPointEnclosure


theorem hierarchicalContributionSplitWitnessPackage_linearizationEnclosure :
    hierarchicalContributionSplitWitnessPackage.certificate.LinearizationEnclosure :=
  hierarchicalContributionSplitWitnessPackage.linearizationEnclosure


theorem hierarchicalContributionSplitWitnessPackage_hyperbolicSplitting :
    hierarchicalContributionSplitWitnessPackage.certificate.HyperbolicSplitting :=
  hierarchicalContributionSplitWitnessPackage.hyperbolicSplitting


theorem hierarchicalContributionSplitWitnessPackage_orbitEntry :
    hierarchicalContributionSplitWitnessPackage.certificate.OrbitEntry :=
  hierarchicalContributionSplitWitnessPackage.orbitEntry


theorem hierarchicalContributionSplitWitnessPackage_predictedExponent_eq :
    hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent =
      Real.log hierarchicalScale.toReal / Real.log hierarchicalThermalEigenvalue := by
  rfl


theorem hierarchicalContributionSplitWitnessPackage_tail_bound :
    (∑' a, hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) ≤
      (∑ a ∈ hierarchicalContributionSplitWitnessPackage.tailCertificate.finitePrefix,
        hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) +
        hierarchicalContributionSplitWitnessPackage.tailCertificate.tailBound :=
  hierarchicalContributionSplitWitnessPackage.tail_tsum_le_prefix_add_tailBound


theorem contributionSplitWitnessPackage_tail_bound_concrete :
    (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤
      (11 : ℝ) / 5 := by
  have h := contributionSplitWitnessPackage.tail_tsum_le_prefix_add_tailBound
  norm_num [contributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit] at h ⊢


theorem contributionSplitWitnessPackage_tailCertifiedTotalBound_eq :
    contributionSplitWitnessPackage.tailCertifiedTotalBound = (11 : ℝ) / 5 := by
  norm_num [FiniteWitnessPackage.tailCertifiedTotalBound,
    FiniteWitnessPackage.tailPrefixSum, FiniteWitnessPackage.tailBudget,
    contributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit]


theorem contributionSplitWitnessPackage_tail_tsum_le_certifiedTotalBound :
    (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤
      contributionSplitWitnessPackage.tailCertifiedTotalBound :=
  contributionSplitWitnessPackage.tail_tsum_le_certifiedTotalBound


theorem contributionSplitWitnessPackage_tail_tsum_le_three_from_totalBound :
    (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤
      (3 : ℝ) :=
  contributionSplitWitnessPackage.tail_tsum_le_of_certifiedTotalBound_le
    (by
      rw [contributionSplitWitnessPackage_tailCertifiedTotalBound_eq]
      norm_num)


theorem contributionSplitWitnessPackage_tailTotalTsum_le_certifiedTotalBound :
    contributionSplitWitnessPackage.tailTotalTsum ≤
      contributionSplitWitnessPackage.tailCertifiedTotalBound :=
  contributionSplitWitnessPackage.tailTotalTsum_le_certifiedTotalBound


theorem contributionSplitWitnessPackage_tailTotalTsum_split :
    contributionSplitWitnessPackage.tailTotalTsum =
      contributionSplitWitnessPackage.tailPrefixSum +
        contributionSplitWitnessPackage.tailRemainderSum :=
  contributionSplitWitnessPackage.tailTotalTsum_eq_prefix_add_remainder


end FiniteWitnessPackageExample
end Exact3D
end StatMech
