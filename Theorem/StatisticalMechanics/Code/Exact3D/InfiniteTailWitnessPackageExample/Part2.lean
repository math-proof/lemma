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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackageExample

theorem geometricTailWitnessPackageFromEnvelope_finiteChecks :
    geometricTailWitnessPackageFromEnvelope.certificate.FiniteChecks :=
  geometricTailWitnessPackageFromEnvelope.finiteChecks


theorem geometricTailWitnessPackageFromEnvelope_finiteCaseChecks :
    geometricTailWitnessPackageFromEnvelope.certificate.FiniteCaseChecks :=
  geometricTailWitnessPackageFromEnvelope.finiteCaseChecks


theorem geometricTailWitnessPackageFromEnvelope_tailBounds :
    geometricTailWitnessPackageFromEnvelope.certificate.TailBounds :=
  geometricTailWitnessPackageFromEnvelope.tailBounds


theorem geometricTailWitnessPackageFromEnvelope_fixedPointEnclosure :
    geometricTailWitnessPackageFromEnvelope.certificate.FixedPointEnclosure :=
  geometricTailWitnessPackageFromEnvelope.fixedPointEnclosure


theorem geometricTailWitnessPackageFromEnvelope_linearizationEnclosure :
    geometricTailWitnessPackageFromEnvelope.certificate.LinearizationEnclosure :=
  geometricTailWitnessPackageFromEnvelope.linearizationEnclosure


theorem geometricTailWitnessPackageFromEnvelope_hyperbolicSplitting :
    geometricTailWitnessPackageFromEnvelope.certificate.HyperbolicSplitting :=
  geometricTailWitnessPackageFromEnvelope.hyperbolicSplitting


theorem geometricTailWitnessPackageFromEnvelope_orbitEntry :
    geometricTailWitnessPackageFromEnvelope.certificate.OrbitEntry :=
  geometricTailWitnessPackageFromEnvelope.orbitEntry


theorem geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_eq_one :
    geometricTailWitnessPackageFromEnvelope.tailCertifiedTotalBound = 1 := by
  norm_num [geometricTailWitnessPackageFromEnvelope,
    InfiniteTailWitnessPackage.ofTailEnvelope,
    InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.tailBudget,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope,
    TailSummability.InfiniteTailCertificate.prefixSum]


theorem geometricTailWitnessPackageFromEnvelope_tail_tsum_le_one :
    (∑' n : ℕ,
      geometricTailWitnessPackageFromEnvelope.tailCertificate.weight n) ≤
      1 := by
  rw [← geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_eq_one]
  exact geometricTailWitnessPackageFromEnvelope.tail_tsum_le_certifiedTotalBound


theorem geometricTailWitnessPackageFromEnvelope_tailTotalTsum_le_one :
    geometricTailWitnessPackageFromEnvelope.tailTotalTsum ≤ 1 := by
  rw [← geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_eq_one]
  exact
    geometricTailWitnessPackageFromEnvelope.tailTotalTsum_le_certifiedTotalBound


theorem geometricTailWitnessPackageFromEnvelope_tailTotalTsum_split :
    geometricTailWitnessPackageFromEnvelope.tailTotalTsum =
      geometricTailWitnessPackageFromEnvelope.tailPrefixSum +
        geometricTailWitnessPackageFromEnvelope.tailRemainderSum :=
  geometricTailWitnessPackageFromEnvelope.tailTotalTsum_eq_prefix_add_remainder


theorem geometricTailWitnessPackageFromEnvelope_tailTotalTsum_eq_tsum :
    geometricTailWitnessPackageFromEnvelope.tailTotalTsum =
      (∑' n : ℕ,
        geometricTailWitnessPackageFromEnvelope.tailCertificate.weight n) :=
  geometricTailWitnessPackageFromEnvelope.tailTotalTsum_eq_tsum


theorem geometricTailWitnessPackageFromEnvelope_summable_tailContribution :
    Summable geometricTailWitnessPackageFromEnvelope.tailContribution :=
  geometricTailWitnessPackageFromEnvelope.summable_tailContribution


theorem geometricTailWitnessPackageFromEnvelope_tailContribution_nonneg
    (n : ℕ) :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailContribution n :=
  geometricTailWitnessPackageFromEnvelope.tailContribution_nonneg n


theorem geometricTailWitnessPackageFromEnvelope_tailPrefixSum_nonneg :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailPrefixSum :=
  geometricTailWitnessPackageFromEnvelope.tailPrefixSum_nonneg


theorem geometricTailWitnessPackageFromEnvelope_tailBudget_nonneg :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailBudget :=
  geometricTailWitnessPackageFromEnvelope.tailBudget_nonneg


theorem geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_nonneg :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailCertifiedTotalBound :=
  geometricTailWitnessPackageFromEnvelope.tailCertifiedTotalBound_nonneg


theorem geometricTailWitnessPackageFromEnvelope_tail_tsum_nonneg :
    0 ≤
      (∑' n : ℕ,
        geometricTailWitnessPackageFromEnvelope.tailCertificate.weight n) :=
  geometricTailWitnessPackageFromEnvelope.tail_tsum_nonneg


theorem geometricTailWitnessPackageFromEnvelope_tailTotalTsum_nonneg :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailTotalTsum :=
  geometricTailWitnessPackageFromEnvelope.tailTotalTsum_nonneg


theorem geometricTailWitnessPackageFromEnvelope_tailRemainderSum_le_tailBudget :
    geometricTailWitnessPackageFromEnvelope.tailRemainderSum ≤
      geometricTailWitnessPackageFromEnvelope.tailBudget :=
  geometricTailWitnessPackageFromEnvelope.tailRemainderSum_le_tailBudget


theorem geometricTailWitnessPackageFromEnvelope_tailRemainderSum_nonneg :
    0 ≤ geometricTailWitnessPackageFromEnvelope.tailRemainderSum :=
  geometricTailWitnessPackageFromEnvelope.tailRemainderSum_nonneg


theorem geometricTailWitnessPackageFromEnvelope_stable_fixedPoint_mem :
    FiniteContraction.ClosedBall
      geometricTailWitnessPackageFromEnvelope.stable.contraction.center
      geometricTailWitnessPackageFromEnvelope.stable.contraction.radius
      geometricTailWitnessPackageFromEnvelope.stable.fixedPoint :=
  geometricTailWitnessPackageFromEnvelope.stable_fixedPoint_mem


theorem geometricTailWitnessPackageFromEnvelope_stable_exists_unique_fixedPoint :
    ∃! p : Fin geometricTailWitnessPackageFromEnvelope.nStable → ℝ,
      geometricTailWitnessPackageFromEnvelope.stable.map p = p :=
  geometricTailWitnessPackageFromEnvelope.stable_exists_unique_fixedPoint


theorem geometricTailWitnessPackageFromEnvelope_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricTailWitnessPackageFromEnvelope.certificate.RGToExponentBridge
        correlationLength) :
    geometricTailWitnessPackageFromEnvelope.certificate.Valid
      correlationLength :=
  geometricTailWitnessPackageFromEnvelope.valid_of_bridge hbridge


theorem geometricTailWitnessPackageFromEnvelope_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricTailWitnessPackageFromEnvelope.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      geometricTailWitnessPackageFromEnvelope.certificate.predictedExponent :=
  geometricTailWitnessPackageFromEnvelope.hasCriticalNu_of_bridge hbridge


theorem
    geometricTailWitnessPackageFromEnvelope_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricTailWitnessPackageFromEnvelope.certificate.predictedExponent) :
    geometricTailWitnessPackageFromEnvelope.certificate.RGToExponentBridge
      correlationLength :=
  geometricTailWitnessPackageFromEnvelope.rgToExponentBridge_of_hasCriticalNu
    hν


theorem geometricTailWitnessPackageFromEnvelope_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricTailWitnessPackageFromEnvelope.certificate.predictedExponent) :
    geometricTailWitnessPackageFromEnvelope.certificate.Valid
      correlationLength :=
  geometricTailWitnessPackageFromEnvelope.valid_of_hasCriticalNu hν


end InfiniteTailWitnessPackageExample
end Exact3D
end StatMech
