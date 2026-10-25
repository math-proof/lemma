/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


@[simp] theorem tableCertifiedTotalBound_eq
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tableCertifiedTotalBound = W.tablePrefixBudget + W.tailBound :=
  rfl

@[simp] theorem retarget_tableFiniteBudget {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tableFiniteBudget = W.tableFiniteBudget :=
  rfl

@[simp] theorem retarget_tablePrefixBudget {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tablePrefixBudget = W.tablePrefixBudget :=
  rfl

@[simp] theorem retarget_tableCertifiedTotalBound {κ : Type*}
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (N : CriticalModel κ) :
    (W.retarget N).tableCertifiedTotalBound =
      W.tableCertifiedTotalBound :=
  rfl


theorem tableCertifiedTotalBound_nonneg_of_component_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (hfinite : 0 ≤ W.finiteBound) (hprefix : 0 ≤ W.prefixTailBound) :
    0 ≤ W.tableCertifiedTotalBound := by
  have hcard : 0 ≤ (W.finitePrefix.card : ℝ) := by positivity
  have hfiniteBudget : 0 ≤ W.tableFiniteBudget := by
    exact mul_nonneg hcard hfinite
  have hprefixBudget : 0 ≤ W.tablePrefixBudget := by
    exact add_nonneg hfiniteBudget hprefix
  exact add_nonneg hprefixBudget (by
    simpa [tailBudget] using W.tailBudget_nonneg)


theorem tableTailBound_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailBound := by
  simpa [tailBudget] using W.tailBudget_nonneg


theorem tableCertifiedTotalBound_le_of_component_bounds
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
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
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixBound tailBound' : ℝ}
    (hprefix : W.tablePrefixBudget ≤ prefixBound)
    (htail : W.tailBound ≤ tailBound') :
    W.tableCertifiedTotalBound ≤ prefixBound + tailBound' := by
  simpa [tableCertifiedTotalBound_eq] using add_le_add hprefix htail


theorem tailPrefixSum_le_tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailPrefixSum ≤ W.tablePrefixBudget := by
  simpa [tailPrefixSum, tablePrefixBudget, tableFiniteBudget,
    toWitnessPackage, InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.ofContributionSplitMaskedTailEnvelope,
    ContributionSplit.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix,
    TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope,
    TailSummability.InfiniteTailCertificate.prefixSum] using
    (W.S.total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn
      W.finitePrefix W.tailEnvelope W.additive W.finiteTable
      W.tailEnvelopeOnPrefix W.prefixTailEnvelopeSum_le)


theorem finiteContribution_le_finiteBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (a : α) :
    W.S.finiteContribution a ≤ W.finiteBound :=
  finite_le_of_tableUpperBound W.finiteTable a


theorem tablePrefixBudget_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tablePrefixBudget :=
  le_trans W.tailPrefixSum_nonneg W.tailPrefixSum_le_tablePrefixBudget


theorem tailCertifiedTotalBound_le_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailCertifiedTotalBound ≤ W.tableCertifiedTotalBound := by
  change W.tailPrefixSum + W.tailBudget ≤ W.tablePrefixBudget + W.tailBound
  rw [W.tailBudget_eq_tailBound]
  exact add_le_add W.tailPrefixSum_le_tablePrefixBudget (le_refl W.tailBound)


theorem tail_tsum_le_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tableCertifiedTotalBound :=
  le_trans W.tail_tsum_le_certifiedTotalBound
    W.tailCertifiedTotalBound_le_tableCertifiedTotalBound


theorem tail_tsum_le_of_tableCertifiedTotalBound_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tableCertifiedTotalBound ≤ B) :
    (∑' a, W.tailContribution a) ≤ B :=
  le_trans W.tail_tsum_le_tableCertifiedTotalBound hB


theorem tail_tsum_le_tablePrefixBudget_add_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tablePrefixBudget + W.tailBound := by
  simpa [tableCertifiedTotalBound_eq] using
    W.tail_tsum_le_tableCertifiedTotalBound


theorem tailTotalTsum_le_tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum ≤ W.tableCertifiedTotalBound :=
  le_trans W.tailTotalTsum_le_certifiedTotalBound
    W.tailCertifiedTotalBound_le_tableCertifiedTotalBound


theorem tableCertifiedTotalBound_nonneg
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tableCertifiedTotalBound :=
  le_trans W.tailTotalTsum_nonneg W.tailTotalTsum_le_tableCertifiedTotalBound


theorem tailTotalTsum_le_tablePrefixBudget_add_tailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum ≤ W.tablePrefixBudget + W.tailBound := by
  simpa [tableCertifiedTotalBound_eq] using
    W.tailTotalTsum_le_tableCertifiedTotalBound


theorem tailTotalTsum_le_of_tableCertifiedTotalBound_le
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tableCertifiedTotalBound ≤ B) :
    W.tailTotalTsum ≤ B :=
  le_trans W.tailTotalTsum_le_tableCertifiedTotalBound hB


end InfiniteTailMaskedTableWitnessPackage
end Exact3D
end StatMech
