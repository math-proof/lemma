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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part6
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackageExample

theorem geometricContributionSplitTailEnvelopeWitnessPackage_finiteChecks :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.FiniteChecks :=
  geometricContributionSplitTailEnvelopeWitnessPackage.finiteChecks


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_finiteCaseChecks :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.FiniteCaseChecks :=
  geometricContributionSplitTailEnvelopeWitnessPackage.finiteCaseChecks


theorem geometricContributionSplitTailEnvelopeWitnessPackage_tailBounds :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.TailBounds :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailBounds


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_fixedPointEnclosure :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.FixedPointEnclosure :=
  geometricContributionSplitTailEnvelopeWitnessPackage.fixedPointEnclosure


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_linearizationEnclosure :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.LinearizationEnclosure :=
  geometricContributionSplitTailEnvelopeWitnessPackage.linearizationEnclosure


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_hyperbolicSplitting :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.HyperbolicSplitting :=
  geometricContributionSplitTailEnvelopeWitnessPackage.hyperbolicSplitting


theorem geometricContributionSplitTailEnvelopeWitnessPackage_orbitEntry :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.OrbitEntry :=
  geometricContributionSplitTailEnvelopeWitnessPackage.orbitEntry


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_eq_one :
    geometricContributionSplitTailEnvelopeWitnessPackage.tailCertifiedTotalBound =
      1 := by
  norm_num [geometricContributionSplitTailEnvelopeWitnessPackage,
    InfiniteTailWitnessPackage.ofContributionSplitTailEnvelope,
    InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.tailBudget,
    ContributionSplit.infiniteTailCertificate_of_tailEnvelope_off_prefix,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope,
    TailSummability.InfiniteTailCertificate.prefixSum,
    geometricContributionSplit]


theorem geometricContributionSplitTailEnvelopeWitnessPackage_tail_tsum_le_one :
    (∑' n : ℕ,
      geometricContributionSplitTailEnvelopeWitnessPackage.tailCertificate.weight
        n) ≤ 1 := by
  rw [←
    geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact
    geometricContributionSplitTailEnvelopeWitnessPackage.tail_tsum_le_certifiedTotalBound


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_le_one :
    geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum ≤
      1 := by
  rw [←
    geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact
    geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum_le_certifiedTotalBound


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_split :
    geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum =
      geometricContributionSplitTailEnvelopeWitnessPackage.tailPrefixSum +
        geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum_eq_prefix_add_remainder


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_eq_tsum :
    geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum =
      (∑' n : ℕ,
        geometricContributionSplitTailEnvelopeWitnessPackage.tailCertificate.weight n) :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum_eq_tsum


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_summable_tailContribution :
    Summable
      geometricContributionSplitTailEnvelopeWitnessPackage.tailContribution :=
  geometricContributionSplitTailEnvelopeWitnessPackage.summable_tailContribution


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailContribution_nonneg
    (n : ℕ) :
    0 ≤
      geometricContributionSplitTailEnvelopeWitnessPackage.tailContribution n :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailContribution_nonneg n


theorem geometricContributionSplitTailEnvelopeWitnessPackage_tailPrefixSum_nonneg :
    0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailPrefixSum :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailPrefixSum_nonneg


theorem geometricContributionSplitTailEnvelopeWitnessPackage_tailBudget_nonneg :
    0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailBudget :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailBudget_nonneg


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_nonneg :
    0 ≤
      geometricContributionSplitTailEnvelopeWitnessPackage.tailCertifiedTotalBound :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailCertifiedTotalBound_nonneg


theorem geometricContributionSplitTailEnvelopeWitnessPackage_tail_tsum_nonneg :
    0 ≤
      (∑' n : ℕ,
        geometricContributionSplitTailEnvelopeWitnessPackage.tailCertificate.weight n) :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tail_tsum_nonneg


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_nonneg :
    0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum_nonneg


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailRemainderSum_le_tailBudget :
    geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum ≤
      geometricContributionSplitTailEnvelopeWitnessPackage.tailBudget :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum_le_tailBudget


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_tailRemainderSum_nonneg :
    0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum :=
  geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum_nonneg


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_stable_fixedPoint_mem :
    FiniteContraction.ClosedBall
      geometricContributionSplitTailEnvelopeWitnessPackage.stable.contraction.center
      geometricContributionSplitTailEnvelopeWitnessPackage.stable.contraction.radius
      geometricContributionSplitTailEnvelopeWitnessPackage.stable.fixedPoint :=
  geometricContributionSplitTailEnvelopeWitnessPackage.stable_fixedPoint_mem


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_stable_exists_unique_fixedPoint :
    ∃! p :
      Fin geometricContributionSplitTailEnvelopeWitnessPackage.nStable → ℝ,
      geometricContributionSplitTailEnvelopeWitnessPackage.stable.map p = p :=
  geometricContributionSplitTailEnvelopeWitnessPackage.stable_exists_unique_fixedPoint


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricContributionSplitTailEnvelopeWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.Valid
      correlationLength :=
  geometricContributionSplitTailEnvelopeWitnessPackage.valid_of_bridge hbridge


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricContributionSplitTailEnvelopeWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      geometricContributionSplitTailEnvelopeWitnessPackage.certificate.predictedExponent :=
  geometricContributionSplitTailEnvelopeWitnessPackage.hasCriticalNu_of_bridge
    hbridge


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricContributionSplitTailEnvelopeWitnessPackage.certificate.predictedExponent) :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.RGToExponentBridge
      correlationLength :=
  geometricContributionSplitTailEnvelopeWitnessPackage.rgToExponentBridge_of_hasCriticalNu
    hν


theorem
    geometricContributionSplitTailEnvelopeWitnessPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricContributionSplitTailEnvelopeWitnessPackage.certificate.predictedExponent) :
    geometricContributionSplitTailEnvelopeWitnessPackage.certificate.Valid
      correlationLength :=
  geometricContributionSplitTailEnvelopeWitnessPackage.valid_of_hasCriticalNu
    hν


end InfiniteTailWitnessPackageExample
end Exact3D
end StatMech
