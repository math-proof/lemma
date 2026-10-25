/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


@[simp] theorem retarget_tailPrefixSum {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem retarget_tailBudget {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailBudget = W.tailBudget :=
  rfl

@[simp] theorem retarget_tailCertifiedTotalBound {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailCertifiedTotalBound = W.tailCertifiedTotalBound :=
  rfl

@[simp] theorem retarget_tailContribution {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailContribution = W.tailContribution :=
  rfl

@[simp] theorem retarget_tailTotalTsum {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailTotalTsum = W.tailTotalTsum :=
  rfl

@[simp] theorem retarget_tailRemainderSum {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailRemainderSum = W.tailRemainderSum :=
  rfl

@[simp] theorem retarget_predictedExponent {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).certificate.predictedExponent =
      W.certificate.predictedExponent :=
  rfl


theorem summable_tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    Summable W.tailContribution := by
  simpa [tailContribution] using W.toWitnessPackage.summable_tailContribution


theorem tailContribution_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (a : α) :
    0 ≤ W.tailContribution a :=
  W.toWitnessPackage.tailContribution_nonneg a


theorem tailPrefixSum_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailPrefixSum := by
  simpa [tailPrefixSum] using W.toWitnessPackage.tailPrefixSum_nonneg


theorem tailBudget_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailBudget := by
  simpa [tailBudget] using W.toWitnessPackage.tailBudget_nonneg


theorem tailCertifiedTotalBound_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailCertifiedTotalBound := by
  simpa [tailCertifiedTotalBound, tailPrefixSum, tailBudget] using
    W.toWitnessPackage.tailCertifiedTotalBound_nonneg


theorem tailTotalTsum_eq_tsum_totalContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum = ∑' a, W.S.totalContribution a := by
  rfl


theorem tailTotalTsum_eq_tsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum = ∑' a, W.tailContribution a := by
  rfl


theorem tailTotalTsum_eq_prefix_add_remainder
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum = W.tailPrefixSum + W.tailRemainderSum := by
  simpa [tailTotalTsum, tailPrefixSum, tailRemainderSum] using
    W.toWitnessPackage.tailTotalTsum_eq_prefix_add_remainder


theorem tail_tsum_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ ∑' a, W.tailContribution a := by
  simpa [tailContribution] using W.toWitnessPackage.tail_tsum_nonneg


theorem tailTotalTsum_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailTotalTsum := by
  simpa [tailTotalTsum] using W.toWitnessPackage.tailTotalTsum_nonneg


theorem tail_tsum_le_prefix_add_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tailPrefixSum + W.tailBudget := by
  simpa [tailContribution, tailPrefixSum, tailBudget] using
    W.toWitnessPackage.tail_tsum_le_prefix_add_tailBound


theorem tailRemainderSum_le_tailBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailRemainderSum ≤ W.tailBudget := by
  simpa [tailRemainderSum, tailBudget] using
    W.toWitnessPackage.tailRemainderSum_le_tailBudget


theorem tailRemainderSum_le_of_tailBudget_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    W.tailRemainderSum ≤ tailBound' :=
  le_trans W.tailRemainderSum_le_tailBudget hle


theorem tailRemainderSum_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailRemainderSum := by
  simpa [tailRemainderSum] using
    W.toWitnessPackage.tailRemainderSum_nonneg


theorem tailRemainderSum_eq_zero_of_tailBudget_eq_zero
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailRemainderSum = 0 := by
  have htailBound : W.tailBound = 0 := by
    simpa [tailBudget] using hbudget
  exact
    le_antisymm (by
      simpa [htailBound] using W.tailRemainderSum_le_tailBudget)
      W.tailRemainderSum_nonneg


theorem tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailTotalTsum = W.tailPrefixSum := by
  rw [W.tailTotalTsum_eq_prefix_add_remainder,
    W.tailRemainderSum_eq_zero_of_tailBudget_eq_zero hbudget, add_zero]


theorem tail_tsum_le_certifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tailCertifiedTotalBound := by
  simpa [tailContribution, tailCertifiedTotalBound, tailPrefixSum,
    tailBudget] using W.toWitnessPackage.tail_tsum_le_certifiedTotalBound


theorem tail_tsum_le_of_certifiedTotalBound_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tailCertifiedTotalBound ≤ B) :
    (∑' a, W.tailContribution a) ≤ B :=
  le_trans W.tail_tsum_le_certifiedTotalBound hB


theorem tailTotalTsum_le_certifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum ≤ W.tailCertifiedTotalBound := by
  simpa [tailTotalTsum, tailCertifiedTotalBound, tailPrefixSum, tailBudget] using
    W.toWitnessPackage.tailTotalTsum_le_certifiedTotalBound


theorem tailTotalTsum_le_of_certifiedTotalBound_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tailCertifiedTotalBound ≤ B) :
    W.tailTotalTsum ≤ B :=
  le_trans W.tailTotalTsum_le_certifiedTotalBound hB


theorem tail_tsum_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    (∑' a, W.tailContribution a) ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailContribution, tailPrefixSum, tailBudget] using
    W.toWitnessPackage.tail_tsum_le_prefix_add_of_tailBudget_le hle


theorem tailTotalTsum_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    W.tailTotalTsum ≤ W.tailPrefixSum + tailBound' := by
  simpa [W.tailTotalTsum_eq_tsum] using
    W.tail_tsum_le_prefix_add_of_tailBudget_le hle


theorem tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    W.tailCertifiedTotalBound ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailCertifiedTotalBound] using
    add_le_add (le_refl W.tailPrefixSum) hle


end InfiniteTailMaskedTableWitnessPackage
end Exact3D
end StatMech
