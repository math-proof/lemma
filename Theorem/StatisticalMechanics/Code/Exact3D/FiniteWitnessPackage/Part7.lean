/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part7
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


@[simp] theorem retarget_tailPrefixSum {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailPrefixSum = W.tailPrefixSum :=
  rfl


@[simp] theorem retarget_tailBudget {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailBudget = W.tailBudget :=
  rfl


@[simp] theorem retarget_tailCertifiedTotalBound {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailCertifiedTotalBound =
      W.tailCertifiedTotalBound :=
  rfl


@[simp] theorem retarget_tailContribution {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailContribution = W.tailContribution :=
  rfl


@[simp] theorem retarget_tailTotalTsum {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailTotalTsum = W.tailTotalTsum :=
  rfl


@[simp] theorem retarget_tailSupport {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailSupport = W.tailSupport :=
  rfl


@[simp] theorem retarget_tailRemainderSum {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailRemainderSum = W.tailRemainderSum :=
  rfl


@[simp] theorem retarget_tailEnvelopeSum {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).tailEnvelopeSum = W.tailEnvelopeSum :=
  rfl


@[simp] theorem retarget_predictedExponent {κ : Type*}
    (W : FiniteWitnessPackage (α := α) M) (N : CriticalModel κ) :
    (W.retarget N).certificate.predictedExponent =
      W.certificate.predictedExponent :=
  rfl


theorem tailTotalTsum_eq_tsum
    (W : FiniteWitnessPackage (α := α) M) :
    W.tailTotalTsum = ∑' a, W.tailCertificate.weight a :=
  rfl


theorem tailTotalTsum_eq_prefix_add_remainder
    (W : FiniteWitnessPackage (α := α) M) :
    W.tailTotalTsum = W.tailPrefixSum + W.tailRemainderSum := by
  simpa [tailTotalTsum, tailContribution, tailPrefixSum,
    tailRemainderSum, tailSupport] using
    W.tailCertificate.tsum_eq_prefix_add_tail


theorem tailRemainderSum_le_tailBudget
    (W : FiniteWitnessPackage (α := α) M) :
    W.tailRemainderSum ≤ W.tailBudget := by
  simpa [tailRemainderSum, tailContribution, tailSupport, tailBudget] using
    W.tailCertificate.tail_sum_le_bound


theorem tailRemainderSum_nonneg
    (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ W.tailRemainderSum := by
  simpa [tailRemainderSum, tailContribution, tailSupport] using
    W.tailCertificate.tail_sum_nonneg


theorem tailSupport_eq_empty_of_support_subset
    (W : FiniteWitnessPackage (α := α) M)
    (hsupport_subset_prefix :
      W.tailCertificate.support ⊆ W.tailCertificate.finitePrefix) :
    W.tailSupport = ∅ := by
  simpa [tailSupport] using
    W.tailCertificate.tailSupport_eq_empty_of_support_subset
      hsupport_subset_prefix


theorem tailTotalTsum_eq_tailPrefixSum_of_support_subset
    (W : FiniteWitnessPackage (α := α) M)
    (hsupport_subset_prefix :
      W.tailCertificate.support ⊆ W.tailCertificate.finitePrefix) :
    W.tailTotalTsum = W.tailPrefixSum := by
  simpa [tailTotalTsum, tailContribution, tailPrefixSum] using
    W.tailCertificate.tsum_eq_finitePrefix_sum_of_support_subset
      hsupport_subset_prefix


theorem tailRemainderSum_eq_zero_of_support_subset
    (W : FiniteWitnessPackage (α := α) M)
    (hsupport_subset_prefix :
      W.tailCertificate.support ⊆ W.tailCertificate.finitePrefix) :
    W.tailRemainderSum = 0 := by
  simpa [tailRemainderSum, tailContribution, tailSupport] using
    W.tailCertificate.tail_sum_eq_zero_of_support_subset
      hsupport_subset_prefix


theorem tailRemainderSum_eq_zero_of_tailBudget_eq_zero
    (W : FiniteWitnessPackage (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailRemainderSum = 0 :=
  le_antisymm (by simpa [hbudget] using W.tailRemainderSum_le_tailBudget)
    W.tailRemainderSum_nonneg


theorem tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero
    (W : FiniteWitnessPackage (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailTotalTsum = W.tailPrefixSum := by
  rw [W.tailTotalTsum_eq_prefix_add_remainder,
    W.tailRemainderSum_eq_zero_of_tailBudget_eq_zero hbudget, add_zero]


theorem tailEnvelopeSum_nonneg
    (W : FiniteWitnessPackage (α := α) M) :
    0 ≤ W.tailEnvelopeSum := by
  simpa [tailEnvelopeSum, tailSupport] using
    W.tailCertificate.envelope_tail_sum_nonneg


theorem tailEnvelopeSum_le_tailBudget
    (W : FiniteWitnessPackage (α := α) M) :
    W.tailEnvelopeSum ≤ W.tailBudget := by
  simpa [tailEnvelopeSum, tailSupport, tailBudget] using
    W.tailCertificate.envelope_tail_sum_le


theorem tail_tsum_le_prefix_add_tailBound
    (W : FiniteWitnessPackage (α := α) M) :
    (∑' a, W.tailCertificate.weight a) ≤
      (∑ a ∈ W.tailCertificate.finitePrefix,
        W.tailCertificate.weight a) + W.tailCertificate.tailBound :=
  W.tailCertificate.tsum_le_prefix_sum_add_tailBound


theorem tail_tsum_le_certifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) :
    (∑' a, W.tailCertificate.weight a) ≤ W.tailCertifiedTotalBound := by
  simpa [tailCertifiedTotalBound, tailPrefixSum, tailBudget] using
    W.tail_tsum_le_prefix_add_tailBound


theorem tail_tsum_le_of_certifiedTotalBound_le
    (W : FiniteWitnessPackage (α := α) M) {B : ℝ}
    (hB : W.tailCertifiedTotalBound ≤ B) :
    (∑' a, W.tailCertificate.weight a) ≤ B :=
  le_trans W.tail_tsum_le_certifiedTotalBound hB


theorem tailTotalTsum_le_certifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) :
    W.tailTotalTsum ≤ W.tailCertifiedTotalBound := by
  simpa [tailTotalTsum, tailContribution] using
    W.tail_tsum_le_certifiedTotalBound


theorem tailTotalTsum_le_of_certifiedTotalBound_le
    (W : FiniteWitnessPackage (α := α) M) {B : ℝ}
    (hB : W.tailCertifiedTotalBound ≤ B) :
    W.tailTotalTsum ≤ B :=
  le_trans W.tailTotalTsum_le_certifiedTotalBound hB


end FiniteWitnessPackage
end Exact3D
end StatMech
