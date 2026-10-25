/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


@[simp] theorem retarget_tailPrefixSum {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailPrefixSum = W.tailPrefixSum :=
  rfl


@[simp] theorem retarget_tailBudget {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailBudget = W.tailBudget :=
  rfl


@[simp] theorem retarget_tailCertifiedTotalBound {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailCertifiedTotalBound =
      W.tailCertifiedTotalBound :=
  rfl


@[simp] theorem retarget_tailContribution {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailContribution = W.tailContribution :=
  rfl


@[simp] theorem retarget_tailTotalTsum {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailTotalTsum = W.tailTotalTsum :=
  rfl


@[simp] theorem retarget_tailRemainderSum {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailRemainderSum = W.tailRemainderSum :=
  rfl


@[simp] theorem retarget_predictedExponent {κ : Type*}
    (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).certificate.predictedExponent =
      W.certificate.predictedExponent :=
  rfl


theorem tailTotalTsum_eq_tsum
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.tailTotalTsum = ∑' a, W.tailCertificate.weight a :=
  rfl


theorem tailContribution_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) (a : α) :
    0 ≤ W.tailContribution a :=
  W.tailCertificate.weight_nonneg a


theorem tailContribution_decomposition
    (W : InfiniteTailWitnessPackage (α := α) M) (a : α) :
    W.tailContribution a =
      W.tailCertificate.prefixWeight a + W.tailCertificate.tailWeight a := by
  simpa [tailContribution] using W.tailCertificate.decomposition a


theorem tailTotalTsum_eq_prefix_add_remainder
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.tailTotalTsum = W.tailPrefixSum + W.tailRemainderSum := by
  simpa [tailTotalTsum, tailContribution, tailPrefixSum,
    tailRemainderSum] using
    W.tailCertificate.tsum_weight_eq_prefixSum_add_tail


theorem tailRemainderSum_le_tailBudget
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.tailRemainderSum ≤ W.tailBudget := by
  simpa [tailRemainderSum, tailBudget] using
    W.tailCertificate.tail_tsum_le


theorem tailRemainderSum_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ W.tailRemainderSum := by
  simpa [tailRemainderSum] using
    W.tailCertificate.tail_tsum_nonneg


theorem tailRemainderSum_eq_zero_of_tailBudget_eq_zero
    (W : InfiniteTailWitnessPackage (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailRemainderSum = 0 :=
  le_antisymm (by simpa [hbudget] using W.tailRemainderSum_le_tailBudget)
    W.tailRemainderSum_nonneg


theorem tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero
    (W : InfiniteTailWitnessPackage (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailTotalTsum = W.tailPrefixSum := by
  rw [W.tailTotalTsum_eq_prefix_add_remainder,
    W.tailRemainderSum_eq_zero_of_tailBudget_eq_zero hbudget, add_zero]


theorem tail_tsum_le_prefix_add_tailBound
    (W : InfiniteTailWitnessPackage (α := α) M) :
    (∑' a, W.tailCertificate.weight a) ≤
      W.tailCertificate.prefixSum + W.tailCertificate.tailBound :=
  W.tailCertificate.tsum_weight_le_prefixSum_add_tailBound


theorem tail_tsum_le_certifiedTotalBound
    (W : InfiniteTailWitnessPackage (α := α) M) :
    (∑' a, W.tailCertificate.weight a) ≤ W.tailCertifiedTotalBound := by
  simpa [tailCertifiedTotalBound, tailPrefixSum, tailBudget] using
    W.tail_tsum_le_prefix_add_tailBound


theorem tail_tsum_le_of_certifiedTotalBound_le
    (W : InfiniteTailWitnessPackage (α := α) M) {B : ℝ}
    (hB : W.tailCertifiedTotalBound ≤ B) :
    (∑' a, W.tailCertificate.weight a) ≤ B :=
  le_trans W.tail_tsum_le_certifiedTotalBound hB


theorem tailTotalTsum_le_certifiedTotalBound
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.tailTotalTsum ≤ W.tailCertifiedTotalBound := by
  simpa [tailTotalTsum, tailContribution] using
    W.tail_tsum_le_certifiedTotalBound


theorem tailTotalTsum_le_of_certifiedTotalBound_le
    (W : InfiniteTailWitnessPackage (α := α) M) {B : ℝ}
    (hB : W.tailCertifiedTotalBound ≤ B) :
    W.tailTotalTsum ≤ B :=
  le_trans W.tailTotalTsum_le_certifiedTotalBound hB


theorem tail_tsum_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    (∑' a, W.tailCertificate.weight a) ≤
      W.tailPrefixSum + tailBound' := by
  calc
    (∑' a, W.tailCertificate.weight a) ≤
        W.tailPrefixSum + W.tailBudget := by
      simpa [tailPrefixSum, tailBudget] using
        W.tail_tsum_le_prefix_add_tailBound
    _ ≤ W.tailPrefixSum + tailBound' :=
      add_le_add (le_refl W.tailPrefixSum) hle


theorem tailTotalTsum_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailTotalTsum ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailTotalTsum, tailContribution] using
    W.tail_tsum_le_prefix_add_of_tailBudget_le hle


theorem tailRemainderSum_le_of_tailBudget_le
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailRemainderSum ≤ tailBound' :=
  le_trans W.tailRemainderSum_le_tailBudget hle


theorem tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailWitnessPackage (α := α) M) {tailBound' : ℝ}
    (hle : W.tailBudget ≤ tailBound') :
    W.tailCertifiedTotalBound ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailCertifiedTotalBound] using
    add_le_add (le_refl W.tailPrefixSum) hle

@[simp] theorem ofFiniteWitnessPackage_tailPrefixSum
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailPrefixSum = W.tailPrefixSum := by
  rfl

@[simp] theorem ofFiniteWitnessPackage_tailBudget
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailBudget = W.tailBudget := by
  rfl

@[simp] theorem ofFiniteWitnessPackage_tailCertifiedTotalBound
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailCertifiedTotalBound =
      W.tailCertifiedTotalBound := by
  rfl

@[simp] theorem ofFiniteWitnessPackage_tailContribution
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailContribution = W.tailContribution :=
  rfl

@[simp] theorem ofFiniteWitnessPackage_tailTotalTsum
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailTotalTsum = W.tailTotalTsum :=
  rfl


theorem ofFiniteWitnessPackage_tailRemainderSum
    (W : FiniteWitnessPackage (α := α) M) :
    (ofFiniteWitnessPackage W).tailRemainderSum = W.tailRemainderSum := by
  have hInf :=
    (ofFiniteWitnessPackage W).tailTotalTsum_eq_prefix_add_remainder
  have hFin := W.tailTotalTsum_eq_prefix_add_remainder
  rw [ofFiniteWitnessPackage_tailTotalTsum,
    ofFiniteWitnessPackage_tailPrefixSum] at hInf
  linarith


theorem tailPrefixSum_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ W.tailPrefixSum := by
  simpa [tailPrefixSum] using W.tailCertificate.prefixSum_nonneg


theorem tailBudget_nonneg (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ W.tailBudget := by
  simpa [tailBudget] using W.tailCertificate.tailBound_nonneg


theorem tailCertifiedTotalBound_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ W.tailCertifiedTotalBound :=
  add_nonneg W.tailPrefixSum_nonneg W.tailBudget_nonneg


theorem tail_tsum_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ ∑' a, W.tailCertificate.weight a :=
  W.tailCertificate.tsum_weight_nonneg


theorem tailTotalTsum_nonneg
    (W : InfiniteTailWitnessPackage (α := α) M) :
    0 ≤ W.tailTotalTsum := by
  simpa [tailTotalTsum, tailContribution] using W.tail_tsum_nonneg


end InfiniteTailWitnessPackage
end Exact3D
end StatMech
