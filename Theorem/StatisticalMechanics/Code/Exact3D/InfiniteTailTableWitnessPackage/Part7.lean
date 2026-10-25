/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part8
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


@[simp] theorem tableCertifiedTotalBound_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tableCertifiedTotalBound = W.tablePrefixBudget + W.tailBound :=
  rfl

@[simp] theorem retarget_tailPrefixSum {κ : Type*}
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailPrefixSum = W.tailPrefixSum :=
  rfl

@[simp] theorem retarget_tailBudget {κ : Type*}
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailBudget = W.tailBudget :=
  rfl

@[simp] theorem retarget_tailCertifiedTotalBound {κ : Type*}
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailCertifiedTotalBound = W.tailCertifiedTotalBound :=
  rfl

@[simp] theorem retarget_tailRemainderSum {κ : Type*}
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailRemainderSum = W.tailRemainderSum :=
  rfl

@[simp] theorem retarget_tailContribution {κ : Type*}
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailContribution = W.tailContribution :=
  rfl

@[simp] theorem retarget_tailTotalTsum {κ : Type*}
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tailTotalTsum = W.tailTotalTsum :=
  rfl

@[simp] theorem retarget_tableFiniteBudget {κ : Type*}
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tableFiniteBudget = W.tableFiniteBudget :=
  rfl

@[simp] theorem retarget_tablePrefixBudget {κ : Type*}
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tablePrefixBudget = W.tablePrefixBudget :=
  rfl

@[simp] theorem retarget_tableCertifiedTotalBound {κ : Type*}
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tableCertifiedTotalBound = W.tableCertifiedTotalBound :=
  rfl

@[simp] theorem retarget_predictedExponent {κ : Type*}
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).certificate.predictedExponent =
      W.certificate.predictedExponent :=
  rfl


theorem tableCertifiedTotalBound_le_of_component_bounds
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' prefixTailBound' tailBound' : ℝ}
    (hfinite : W.finiteBound ≤ finiteBound')
    (hprefix : W.prefixTailBound ≤ prefixTailBound')
    (htail : W.tailBound ≤ tailBound') :
    W.tableCertifiedTotalBound ≤
      (W.finitePrefix.card : ℝ) * finiteBound' +
        prefixTailBound' + tailBound' := by
  have hcard : 0 ≤ (W.finitePrefix.card : ℝ) := by positivity
  have hfiniteBudget :
      (W.finitePrefix.card : ℝ) * W.finiteBound ≤
        (W.finitePrefix.card : ℝ) * finiteBound' :=
    mul_le_mul_of_nonneg_left hfinite hcard
  exact add_le_add (add_le_add hfiniteBudget hprefix) htail


theorem tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {prefixBound tailBound' : ℝ}
    (hprefix : W.tablePrefixBudget ≤ prefixBound)
    (htail : W.tailBound ≤ tailBound') :
    W.tableCertifiedTotalBound ≤ prefixBound + tailBound' := by
  simpa [tableCertifiedTotalBound_eq] using add_le_add hprefix htail


theorem tailCertifiedTotalBound_le_tableCertifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailCertifiedTotalBound ≤ W.tableCertifiedTotalBound := by
  simpa [tailCertifiedTotalBound, InfiniteTailWitnessPackage.tailCertifiedTotalBound,
    InfiniteTailWitnessPackage.tailBudget, tableCertifiedTotalBound,
    toWitnessPackage, InfiniteTailWitnessPackage.ofContributionSplitTailEnvelope,
    ContributionSplit.infiniteTailCertificate_of_tailEnvelope_off_prefix,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope] using
    add_le_add W.tailPrefixSum_le_tablePrefixBound (le_refl W.tailBound)


theorem tail_tsum_le_tableCertifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tableCertifiedTotalBound :=
  le_trans W.tail_tsum_le_certifiedTotalBound
    W.tailCertifiedTotalBound_le_tableCertifiedTotalBound


theorem tail_tsum_le_of_tableCertifiedTotalBound_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tableCertifiedTotalBound ≤ B) :
    (∑' a, W.tailContribution a) ≤ B :=
  le_trans W.tail_tsum_le_tableCertifiedTotalBound hB


theorem tail_tsum_le_tablePrefixBudget_add_tailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tablePrefixBudget + W.tailBound := by
  simpa [tableCertifiedTotalBound_eq] using
    W.tail_tsum_le_tableCertifiedTotalBound


theorem tailTotalTsum_le_tableCertifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum ≤ W.tableCertifiedTotalBound := by
  simpa [tailTotalTsum, toWitnessPackage, InfiniteTailWitnessPackage.tailTotalTsum,
    InfiniteTailWitnessPackage.tailContribution,
    InfiniteTailWitnessPackage.ofContributionSplitTailEnvelope,
    tableCertifiedTotalBound] using
    (W.S.tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_tailBound
      W.finitePrefix W.tailEnvelope W.total_nonneg W.additive W.finiteTable
      W.tailEnvelopeOnPrefix W.prefixTailEnvelopeSum_le
      W.finite_zero_off_prefix W.tailEnvelope_nonneg
      W.tail_le_tailEnvelope_off_prefix W.summable_tailEnvelope
      W.tailEnvelope_tsum_le)


theorem tableCertifiedTotalBound_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tableCertifiedTotalBound :=
  le_trans W.tailTotalTsum_nonneg W.tailTotalTsum_le_tableCertifiedTotalBound


theorem tailTotalTsum_le_of_tableCertifiedTotalBound_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tableCertifiedTotalBound ≤ B) :
    W.tailTotalTsum ≤ B :=
  le_trans W.tailTotalTsum_le_tableCertifiedTotalBound hB


theorem tailTotalTsum_le_tablePrefixBudget_add_tailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum ≤ W.tablePrefixBudget + W.tailBound := by
  simpa [tableCertifiedTotalBound_eq] using
    W.tailTotalTsum_le_tableCertifiedTotalBound


end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
