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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackageExample

theorem geometricContributionSplitWitnessPackage_finiteChecks :
    geometricContributionSplitWitnessPackage.certificate.FiniteChecks :=
  geometricContributionSplitWitnessPackage.finiteChecks


theorem geometricContributionSplitWitnessPackage_finiteCaseChecks :
    geometricContributionSplitWitnessPackage.certificate.FiniteCaseChecks :=
  geometricContributionSplitWitnessPackage.finiteCaseChecks


theorem geometricContributionSplitWitnessPackage_tailBounds :
    geometricContributionSplitWitnessPackage.certificate.TailBounds :=
  geometricContributionSplitWitnessPackage.tailBounds


theorem geometricContributionSplitWitnessPackage_fixedPointEnclosure :
    geometricContributionSplitWitnessPackage.certificate.FixedPointEnclosure :=
  geometricContributionSplitWitnessPackage.fixedPointEnclosure


theorem geometricContributionSplitWitnessPackage_linearizationEnclosure :
    geometricContributionSplitWitnessPackage.certificate.LinearizationEnclosure :=
  geometricContributionSplitWitnessPackage.linearizationEnclosure


theorem geometricContributionSplitWitnessPackage_hyperbolicSplitting :
    geometricContributionSplitWitnessPackage.certificate.HyperbolicSplitting :=
  geometricContributionSplitWitnessPackage.hyperbolicSplitting


theorem geometricContributionSplitWitnessPackage_orbitEntry :
    geometricContributionSplitWitnessPackage.certificate.OrbitEntry :=
  geometricContributionSplitWitnessPackage.orbitEntry


theorem geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_eq_one :
    geometricContributionSplitWitnessPackage.tailCertifiedTotalBound = 1 := by
  norm_num [geometricContributionSplitWitnessPackage,
    InfiniteTailWitnessPackage.ofContributionSplitInfiniteTail,
    InfiniteTailWitnessPackage.ofTailEnvelope,
    InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.tailBudget,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope,
    TailSummability.InfiniteTailCertificate.prefixSum,
    geometricContributionSplit]


theorem geometricContributionSplitWitnessPackage_tail_tsum_le_one :
    (∑' n : ℕ,
      geometricContributionSplitWitnessPackage.tailCertificate.weight n) ≤
      1 := by
  rw [← geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact geometricContributionSplitWitnessPackage.tail_tsum_le_certifiedTotalBound


theorem geometricContributionSplitWitnessPackage_tailTotalTsum_le_one :
    geometricContributionSplitWitnessPackage.tailTotalTsum ≤ 1 := by
  rw [← geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact
    geometricContributionSplitWitnessPackage.tailTotalTsum_le_certifiedTotalBound


theorem geometricContributionSplitWitnessPackage_tailTotalTsum_split :
    geometricContributionSplitWitnessPackage.tailTotalTsum =
      geometricContributionSplitWitnessPackage.tailPrefixSum +
        geometricContributionSplitWitnessPackage.tailRemainderSum :=
  geometricContributionSplitWitnessPackage.tailTotalTsum_eq_prefix_add_remainder


theorem geometricContributionSplitWitnessPackage_tailTotalTsum_eq_tsum :
    geometricContributionSplitWitnessPackage.tailTotalTsum =
      (∑' n : ℕ,
        geometricContributionSplitWitnessPackage.tailCertificate.weight n) :=
  geometricContributionSplitWitnessPackage.tailTotalTsum_eq_tsum


theorem geometricContributionSplitWitnessPackage_summable_tailContribution :
    Summable geometricContributionSplitWitnessPackage.tailContribution :=
  geometricContributionSplitWitnessPackage.summable_tailContribution


theorem geometricContributionSplitWitnessPackage_tailContribution_nonneg
    (n : ℕ) :
    0 ≤ geometricContributionSplitWitnessPackage.tailContribution n :=
  geometricContributionSplitWitnessPackage.tailContribution_nonneg n


theorem geometricContributionSplitWitnessPackage_tailPrefixSum_nonneg :
    0 ≤ geometricContributionSplitWitnessPackage.tailPrefixSum :=
  geometricContributionSplitWitnessPackage.tailPrefixSum_nonneg


theorem geometricContributionSplitWitnessPackage_tailBudget_nonneg :
    0 ≤ geometricContributionSplitWitnessPackage.tailBudget :=
  geometricContributionSplitWitnessPackage.tailBudget_nonneg


theorem geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_nonneg :
    0 ≤ geometricContributionSplitWitnessPackage.tailCertifiedTotalBound :=
  geometricContributionSplitWitnessPackage.tailCertifiedTotalBound_nonneg


theorem geometricContributionSplitWitnessPackage_tail_tsum_nonneg :
    0 ≤
      (∑' n : ℕ,
        geometricContributionSplitWitnessPackage.tailCertificate.weight n) :=
  geometricContributionSplitWitnessPackage.tail_tsum_nonneg


theorem geometricContributionSplitWitnessPackage_tailTotalTsum_nonneg :
    0 ≤ geometricContributionSplitWitnessPackage.tailTotalTsum :=
  geometricContributionSplitWitnessPackage.tailTotalTsum_nonneg


theorem
    geometricContributionSplitWitnessPackage_tailRemainderSum_le_tailBudget :
    geometricContributionSplitWitnessPackage.tailRemainderSum ≤
      geometricContributionSplitWitnessPackage.tailBudget :=
  geometricContributionSplitWitnessPackage.tailRemainderSum_le_tailBudget


theorem geometricContributionSplitWitnessPackage_tailRemainderSum_nonneg :
    0 ≤ geometricContributionSplitWitnessPackage.tailRemainderSum :=
  geometricContributionSplitWitnessPackage.tailRemainderSum_nonneg


theorem geometricContributionSplitWitnessPackage_stable_fixedPoint_mem :
    FiniteContraction.ClosedBall
      geometricContributionSplitWitnessPackage.stable.contraction.center
      geometricContributionSplitWitnessPackage.stable.contraction.radius
      geometricContributionSplitWitnessPackage.stable.fixedPoint :=
  geometricContributionSplitWitnessPackage.stable_fixedPoint_mem


theorem
    geometricContributionSplitWitnessPackage_stable_exists_unique_fixedPoint :
    ∃! p : Fin geometricContributionSplitWitnessPackage.nStable → ℝ,
      geometricContributionSplitWitnessPackage.stable.map p = p :=
  geometricContributionSplitWitnessPackage.stable_exists_unique_fixedPoint


theorem geometricContributionSplitWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricContributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    geometricContributionSplitWitnessPackage.certificate.Valid
      correlationLength :=
  geometricContributionSplitWitnessPackage.valid_of_bridge hbridge


theorem geometricContributionSplitWitnessPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricContributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      geometricContributionSplitWitnessPackage.certificate.predictedExponent :=
  geometricContributionSplitWitnessPackage.hasCriticalNu_of_bridge hbridge


theorem
    geometricContributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricContributionSplitWitnessPackage.certificate.predictedExponent) :
    geometricContributionSplitWitnessPackage.certificate.RGToExponentBridge
      correlationLength :=
  geometricContributionSplitWitnessPackage.rgToExponentBridge_of_hasCriticalNu
    hν


theorem geometricContributionSplitWitnessPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricContributionSplitWitnessPackage.certificate.predictedExponent) :
    geometricContributionSplitWitnessPackage.certificate.Valid
      correlationLength :=
  geometricContributionSplitWitnessPackage.valid_of_hasCriticalNu hν


end InfiniteTailWitnessPackageExample
end Exact3D
end StatMech
