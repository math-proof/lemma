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
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackageExample

theorem geometricTailWitnessPackage_finiteChecks :
    geometricTailWitnessPackage.certificate.FiniteChecks :=
  geometricTailWitnessPackage.finiteChecks


theorem geometricTailWitnessPackage_finiteCaseChecks :
    geometricTailWitnessPackage.certificate.FiniteCaseChecks :=
  geometricTailWitnessPackage.finiteCaseChecks


theorem geometricTailWitnessPackage_tailBounds :
    geometricTailWitnessPackage.certificate.TailBounds :=
  geometricTailWitnessPackage.tailBounds


theorem geometricTailWitnessPackage_fixedPointEnclosure :
    geometricTailWitnessPackage.certificate.FixedPointEnclosure :=
  geometricTailWitnessPackage.fixedPointEnclosure


theorem geometricTailWitnessPackage_linearizationEnclosure :
    geometricTailWitnessPackage.certificate.LinearizationEnclosure :=
  geometricTailWitnessPackage.linearizationEnclosure


theorem geometricTailWitnessPackage_hyperbolicSplitting :
    geometricTailWitnessPackage.certificate.HyperbolicSplitting :=
  geometricTailWitnessPackage.hyperbolicSplitting


theorem geometricTailWitnessPackage_orbitEntry :
    geometricTailWitnessPackage.certificate.OrbitEntry :=
  geometricTailWitnessPackage.orbitEntry


theorem geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one :
    geometricTailWitnessPackage.tailCertifiedTotalBound = 1 := by
  norm_num [geometricTailWitnessPackage,
    InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.tailBudget,
    TailSummability.InfiniteTailCertificate.prefixSum,
    InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificate]


theorem geometricTailWitnessPackage_tail_tsum_le_one :
    (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) ≤ 1 := by
  rw [← geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact geometricTailWitnessPackage.tail_tsum_le_certifiedTotalBound


theorem geometricTailWitnessPackage_tail_tsum_le_two :
    (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) ≤ 2 :=
  geometricTailWitnessPackage.tail_tsum_le_of_certifiedTotalBound_le
    (by
      rw [geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one]
      norm_num)


theorem geometricTailWitnessPackage_tailTotalTsum_le_one :
    geometricTailWitnessPackage.tailTotalTsum ≤ 1 := by
  rw [← geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one]
  exact geometricTailWitnessPackage.tailTotalTsum_le_certifiedTotalBound


theorem geometricTailWitnessPackage_tailTotalTsum_le_two :
    geometricTailWitnessPackage.tailTotalTsum ≤ 2 := by
  simpa [geometricTailWitnessPackage,
    InfiniteTailWitnessPackage.tailPrefixSum,
    TailSummability.InfiniteTailCertificate.prefixSum,
    InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificate] using
    geometricTailWitnessPackage.tailTotalTsum_le_prefix_add_of_tailBudget_le
      (tailBound' := 2) (by norm_num [geometricTailWitnessPackage,
        InfiniteTailWitnessPackage.tailBudget,
        InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificate])


theorem geometricTailWitnessPackage_tailTotalTsum_split :
    geometricTailWitnessPackage.tailTotalTsum =
      geometricTailWitnessPackage.tailPrefixSum +
        geometricTailWitnessPackage.tailRemainderSum :=
  geometricTailWitnessPackage.tailTotalTsum_eq_prefix_add_remainder


theorem geometricTailWitnessPackage_tailTotalTsum_eq_tsum :
    geometricTailWitnessPackage.tailTotalTsum =
      (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) :=
  geometricTailWitnessPackage.tailTotalTsum_eq_tsum


theorem geometricTailWitnessPackage_summable_tailContribution :
    Summable geometricTailWitnessPackage.tailContribution :=
  geometricTailWitnessPackage.summable_tailContribution


theorem geometricTailWitnessPackage_tailContribution_nonneg (n : ℕ) :
    0 ≤ geometricTailWitnessPackage.tailContribution n :=
  geometricTailWitnessPackage.tailContribution_nonneg n


theorem geometricTailWitnessPackage_tailPrefixSum_nonneg :
    0 ≤ geometricTailWitnessPackage.tailPrefixSum :=
  geometricTailWitnessPackage.tailPrefixSum_nonneg


theorem geometricTailWitnessPackage_tailBudget_nonneg :
    0 ≤ geometricTailWitnessPackage.tailBudget :=
  geometricTailWitnessPackage.tailBudget_nonneg


theorem geometricTailWitnessPackage_tailCertifiedTotalBound_nonneg :
    0 ≤ geometricTailWitnessPackage.tailCertifiedTotalBound :=
  geometricTailWitnessPackage.tailCertifiedTotalBound_nonneg


theorem geometricTailWitnessPackage_tail_tsum_nonneg :
    0 ≤
      (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) :=
  geometricTailWitnessPackage.tail_tsum_nonneg


theorem geometricTailWitnessPackage_tailTotalTsum_nonneg :
    0 ≤ geometricTailWitnessPackage.tailTotalTsum :=
  geometricTailWitnessPackage.tailTotalTsum_nonneg


theorem geometricTailWitnessPackage_tailRemainderSum_le_tailBudget :
    geometricTailWitnessPackage.tailRemainderSum ≤
      geometricTailWitnessPackage.tailBudget :=
  geometricTailWitnessPackage.tailRemainderSum_le_tailBudget


theorem geometricTailWitnessPackage_tailRemainderSum_nonneg :
    0 ≤ geometricTailWitnessPackage.tailRemainderSum :=
  geometricTailWitnessPackage.tailRemainderSum_nonneg


theorem geometricTailWitnessPackage_stable_fixedPoint_mem :
    FiniteContraction.ClosedBall
      geometricTailWitnessPackage.stable.contraction.center
      geometricTailWitnessPackage.stable.contraction.radius
      geometricTailWitnessPackage.stable.fixedPoint :=
  geometricTailWitnessPackage.stable_fixedPoint_mem


theorem geometricTailWitnessPackage_stable_exists_unique_fixedPoint :
    ∃! p : Fin geometricTailWitnessPackage.nStable → ℝ,
      geometricTailWitnessPackage.stable.map p = p :=
  geometricTailWitnessPackage.stable_exists_unique_fixedPoint


theorem geometricTailWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricTailWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    geometricTailWitnessPackage.certificate.Valid correlationLength :=
  geometricTailWitnessPackage.valid_of_bridge hbridge


theorem geometricTailWitnessPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      geometricTailWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
      correlationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_bridge hbridge


theorem geometricTailWitnessPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricTailWitnessPackage.certificate.predictedExponent) :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      correlationLength :=
  geometricTailWitnessPackage.rgToExponentBridge_of_hasCriticalNu hν


theorem geometricTailWitnessPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu
        (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
        correlationLength
        geometricTailWitnessPackage.certificate.predictedExponent) :
    geometricTailWitnessPackage.certificate.Valid correlationLength :=
  geometricTailWitnessPackage.valid_of_hasCriticalNu hν


end InfiniteTailWitnessPackageExample
end Exact3D
end StatMech
