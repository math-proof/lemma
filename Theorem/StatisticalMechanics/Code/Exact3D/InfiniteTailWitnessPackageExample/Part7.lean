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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part7
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackageExample

theorem contributionSplitAsInfiniteTailPackage_certificate_eq :
    contributionSplitAsInfiniteTailPackage.certificate =
      FiniteWitnessPackageExample.contributionSplitWitnessPackage.certificate :=
  rfl


theorem contributionSplitAsInfiniteTailPackage_tailPrefixSum_eq :
    contributionSplitAsInfiniteTailPackage.tailPrefixSum =
      FiniteWitnessPackageExample.contributionSplitWitnessPackage.tailPrefixSum :=
  rfl


theorem contributionSplitAsInfiniteTailPackage_tailBudget_eq :
    contributionSplitAsInfiniteTailPackage.tailBudget =
      FiniteWitnessPackageExample.contributionSplitWitnessPackage.tailBudget :=
  rfl


theorem contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq_finite :
    contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound =
      FiniteWitnessPackageExample.contributionSplitWitnessPackage.tailCertifiedTotalBound :=
  rfl


theorem contributionSplitAsInfiniteTailPackage_finiteChecks :
    contributionSplitAsInfiniteTailPackage.certificate.FiniteChecks := by
  simpa [contributionSplitAsInfiniteTailPackage] using
    FiniteWitnessPackageExample.contributionSplitWitnessPackage_finiteChecks


theorem contributionSplitAsInfiniteTailPackage_finiteCaseChecks :
    contributionSplitAsInfiniteTailPackage.certificate.FiniteCaseChecks :=
  contributionSplitAsInfiniteTailPackage.finiteCaseChecks


theorem contributionSplitAsInfiniteTailPackage_tailBounds :
    contributionSplitAsInfiniteTailPackage.certificate.TailBounds :=
  contributionSplitAsInfiniteTailPackage.tailBounds


theorem contributionSplitAsInfiniteTailPackage_fixedPointEnclosure :
    contributionSplitAsInfiniteTailPackage.certificate.FixedPointEnclosure :=
  contributionSplitAsInfiniteTailPackage.fixedPointEnclosure


theorem contributionSplitAsInfiniteTailPackage_linearizationEnclosure :
    contributionSplitAsInfiniteTailPackage.certificate.LinearizationEnclosure :=
  contributionSplitAsInfiniteTailPackage.linearizationEnclosure


theorem contributionSplitAsInfiniteTailPackage_hyperbolicSplitting :
    contributionSplitAsInfiniteTailPackage.certificate.HyperbolicSplitting :=
  contributionSplitAsInfiniteTailPackage.hyperbolicSplitting


theorem contributionSplitAsInfiniteTailPackage_orbitEntry :
    contributionSplitAsInfiniteTailPackage.certificate.OrbitEntry :=
  contributionSplitAsInfiniteTailPackage.orbitEntry


theorem contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq :
    contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound =
      (11 : ℝ) / 5 := by
  norm_num [contributionSplitAsInfiniteTailPackage,
    InfiniteTailWitnessPackage.ofFiniteWitnessPackage,
    InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.tailBudget,
    TailSummability.InfiniteTailCertificate.prefixSum,
    TailSummability.FiniteSupportCertificate.toInfiniteTailCertificate,
    FiniteWitnessPackageExample.contributionSplitWitnessPackage,
    FiniteWitnessPackage.ofContributionSplitFiniteSupport,
    ContributionSplit.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn,
    TailSummabilityExample.exampleSplit]


theorem contributionSplitAsInfiniteTailPackage_tailTotalTsum_le_certified :
    contributionSplitAsInfiniteTailPackage.tailTotalTsum ≤
      contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound :=
  contributionSplitAsInfiniteTailPackage.tailTotalTsum_le_certifiedTotalBound


theorem contributionSplitAsInfiniteTailPackage_tail_tsum_le_11_div_5 :
    (∑' a : Fin 2,
      contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) ≤
      (11 : ℝ) / 5 := by
  rw [← contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq]
  exact contributionSplitAsInfiniteTailPackage.tail_tsum_le_certifiedTotalBound


theorem contributionSplitAsInfiniteTailPackage_tail_tsum_le_three :
    (∑' a : Fin 2,
      contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) ≤
      (3 : ℝ) :=
  contributionSplitAsInfiniteTailPackage.tail_tsum_le_of_certifiedTotalBound_le
    (by
      rw [contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq]
      norm_num)


theorem contributionSplitAsInfiniteTailPackage_tailTotalTsum_le_11_div_5 :
    contributionSplitAsInfiniteTailPackage.tailTotalTsum ≤
      (11 : ℝ) / 5 := by
  rw [← contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq]
  exact
    contributionSplitAsInfiniteTailPackage.tailTotalTsum_le_certifiedTotalBound


theorem contributionSplitAsInfiniteTailPackage_tailTotalTsum_split :
    contributionSplitAsInfiniteTailPackage.tailTotalTsum =
      contributionSplitAsInfiniteTailPackage.tailPrefixSum +
        contributionSplitAsInfiniteTailPackage.tailRemainderSum :=
  contributionSplitAsInfiniteTailPackage.tailTotalTsum_eq_prefix_add_remainder


theorem contributionSplitAsInfiniteTailPackage_tailTotalTsum_eq_tsum :
    contributionSplitAsInfiniteTailPackage.tailTotalTsum =
      (∑' a : Fin 2,
        contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) :=
  contributionSplitAsInfiniteTailPackage.tailTotalTsum_eq_tsum


theorem contributionSplitAsInfiniteTailPackage_summable_tailContribution :
    Summable contributionSplitAsInfiniteTailPackage.tailContribution :=
  contributionSplitAsInfiniteTailPackage.summable_tailContribution


theorem contributionSplitAsInfiniteTailPackage_tailContribution_nonneg
    (a : Fin 2) :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailContribution a :=
  contributionSplitAsInfiniteTailPackage.tailContribution_nonneg a


theorem contributionSplitAsInfiniteTailPackage_tailPrefixSum_nonneg :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailPrefixSum :=
  contributionSplitAsInfiniteTailPackage.tailPrefixSum_nonneg


theorem contributionSplitAsInfiniteTailPackage_tailBudget_nonneg :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailBudget :=
  contributionSplitAsInfiniteTailPackage.tailBudget_nonneg


theorem contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_nonneg :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound :=
  contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound_nonneg


theorem contributionSplitAsInfiniteTailPackage_tail_tsum_nonneg :
    0 ≤
      (∑' a : Fin 2,
        contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) :=
  contributionSplitAsInfiniteTailPackage.tail_tsum_nonneg


theorem contributionSplitAsInfiniteTailPackage_tailTotalTsum_nonneg :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailTotalTsum :=
  contributionSplitAsInfiniteTailPackage.tailTotalTsum_nonneg


theorem contributionSplitAsInfiniteTailPackage_tailRemainderSum_le_tailBudget :
    contributionSplitAsInfiniteTailPackage.tailRemainderSum ≤
      contributionSplitAsInfiniteTailPackage.tailBudget :=
  contributionSplitAsInfiniteTailPackage.tailRemainderSum_le_tailBudget


theorem contributionSplitAsInfiniteTailPackage_tailRemainderSum_nonneg :
    0 ≤ contributionSplitAsInfiniteTailPackage.tailRemainderSum :=
  contributionSplitAsInfiniteTailPackage.tailRemainderSum_nonneg


theorem contributionSplitAsInfiniteTailPackage_stable_fixedPoint_mem :
    FiniteContraction.ClosedBall
      contributionSplitAsInfiniteTailPackage.stable.contraction.center
      contributionSplitAsInfiniteTailPackage.stable.contraction.radius
      contributionSplitAsInfiniteTailPackage.stable.fixedPoint :=
  contributionSplitAsInfiniteTailPackage.stable_fixedPoint_mem


theorem contributionSplitAsInfiniteTailPackage_stable_exists_unique_fixedPoint :
    ∃! p : Fin contributionSplitAsInfiniteTailPackage.nStable → ℝ,
      contributionSplitAsInfiniteTailPackage.stable.map p = p :=
  contributionSplitAsInfiniteTailPackage.stable_exists_unique_fixedPoint


theorem contributionSplitAsInfiniteTailPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge
        correlationLength) :
    contributionSplitAsInfiniteTailPackage.certificate.Valid
      correlationLength :=
  contributionSplitAsInfiniteTailPackage.valid_of_bridge hbridge


theorem contributionSplitAsInfiniteTailPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      contributionSplitAsInfiniteTailPackage.certificate.predictedExponent :=
  contributionSplitAsInfiniteTailPackage.hasCriticalNu_of_bridge hbridge


theorem
    contributionSplitAsInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        contributionSplitAsInfiniteTailPackage.certificate.predictedExponent) :
    contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge
      correlationLength :=
  contributionSplitAsInfiniteTailPackage.rgToExponentBridge_of_hasCriticalNu
    hν


theorem contributionSplitAsInfiniteTailPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        contributionSplitAsInfiniteTailPackage.certificate.predictedExponent) :
    contributionSplitAsInfiniteTailPackage.certificate.Valid
      correlationLength :=
  contributionSplitAsInfiniteTailPackage.valid_of_hasCriticalNu hν

end InfiniteTailWitnessPackageExample
end Exact3D
end StatMech
