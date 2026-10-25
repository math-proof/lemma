/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part6
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


@[simp] theorem tailBudget_eq_tailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailBudget = W.tailBound :=
  rfl


theorem tailTotalTsum_eq_tsum_totalContribution
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum = ∑' a, W.S.totalContribution a := by
  rfl


theorem tailTotalTsum_eq_tsum
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum = ∑' a, W.tailContribution a := by
  rfl


theorem tailTotalTsum_eq_prefix_add_remainder
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum = W.tailPrefixSum + W.tailRemainderSum := by
  simpa [tailTotalTsum, tailPrefixSum, tailRemainderSum] using
    W.toWitnessPackage.tailTotalTsum_eq_prefix_add_remainder


theorem tailContribution_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (a : α) :
    0 ≤ W.tailContribution a :=
  W.toWitnessPackage.tailContribution_nonneg a


theorem tailPrefixSum_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailPrefixSum := by
  simpa [tailPrefixSum] using W.toWitnessPackage.tailPrefixSum_nonneg


theorem tailBudget_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailBudget := by
  simpa [tailBudget] using W.toWitnessPackage.tailBudget_nonneg


theorem tailRemainderSum_le_tailBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailRemainderSum ≤ W.tailBudget := by
  simpa [tailRemainderSum, tailBudget] using
    W.toWitnessPackage.tailRemainderSum_le_tailBudget


theorem tailRemainderSum_le_of_tailBudget_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    W.tailRemainderSum ≤ tailBound' :=
  le_trans W.tailRemainderSum_le_tailBudget hle


theorem tailRemainderSum_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailRemainderSum := by
  simpa [tailRemainderSum] using
    W.toWitnessPackage.tailRemainderSum_nonneg


theorem tailRemainderSum_eq_zero_of_tailBudget_eq_zero
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailRemainderSum = 0 := by
  have htailBound : W.tailBound = 0 := by
    simpa [tailBudget] using hbudget
  exact
    le_antisymm (by
      simpa [htailBound] using W.tailRemainderSum_le_tailBudget)
      W.tailRemainderSum_nonneg


theorem tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (hbudget : W.tailBudget = 0) :
    W.tailTotalTsum = W.tailPrefixSum := by
  rw [W.tailTotalTsum_eq_prefix_add_remainder,
    W.tailRemainderSum_eq_zero_of_tailBudget_eq_zero hbudget, add_zero]


theorem tailCertifiedTotalBound_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailCertifiedTotalBound := by
  simpa [tailCertifiedTotalBound] using
    W.toWitnessPackage.tailCertifiedTotalBound_nonneg


theorem tailTotalTsum_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailTotalTsum := by
  simpa [tailTotalTsum] using W.toWitnessPackage.tailTotalTsum_nonneg


theorem tail_tsum_le_prefix_add_tailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tailPrefixSum + W.tailBudget := by
  simpa [tailContribution, tailPrefixSum, tailBudget] using
    W.toWitnessPackage.tail_tsum_le_prefix_add_tailBound


theorem tail_tsum_le_certifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    (∑' a, W.tailContribution a) ≤ W.tailCertifiedTotalBound := by
  simpa [tailContribution, tailCertifiedTotalBound] using
    W.toWitnessPackage.tail_tsum_le_certifiedTotalBound


theorem tail_tsum_le_of_certifiedTotalBound_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tailCertifiedTotalBound ≤ B) :
    (∑' a, W.tailContribution a) ≤ B :=
  le_trans W.tail_tsum_le_certifiedTotalBound hB


theorem tail_tsum_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ ∑' a, W.tailContribution a := by
  simpa [tailContribution] using W.toWitnessPackage.tail_tsum_nonneg


theorem tail_tsum_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    (∑' a, W.tailContribution a) ≤ W.tailPrefixSum + tailBound' := by
  simpa [tailContribution, tailPrefixSum, tailBudget] using
    W.toWitnessPackage.tail_tsum_le_prefix_add_of_tailBudget_le hle


theorem tailTotalTsum_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    W.tailTotalTsum ≤ W.tailPrefixSum + tailBound' := by
  simpa [W.tailTotalTsum_eq_tsum] using
    W.tail_tsum_le_prefix_add_of_tailBudget_le hle


theorem tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBudget ≤ tailBound') :
    W.tailCertifiedTotalBound ≤ W.tailPrefixSum + tailBound' := by
  have hle' : W.toWitnessPackage.tailBudget ≤ tailBound' := by
    simpa [tailBudget] using hle
  simpa [tailCertifiedTotalBound, tailPrefixSum] using
    W.toWitnessPackage.tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le
      hle'


theorem tailTotalTsum_le_certifiedTotalBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailTotalTsum ≤ W.tailCertifiedTotalBound := by
  simpa [tailTotalTsum, tailCertifiedTotalBound] using
    W.toWitnessPackage.tailTotalTsum_le_certifiedTotalBound


theorem tailTotalTsum_le_of_certifiedTotalBound_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {B : ℝ} (hB : W.tailCertifiedTotalBound ≤ B) :
    W.tailTotalTsum ≤ B :=
  le_trans W.tailTotalTsum_le_certifiedTotalBound hB


theorem stable_fixedPoint_mem
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    FiniteContraction.ClosedBall
      W.stable.contraction.center W.stable.contraction.radius
      W.stable.fixedPoint :=
  W.stable.fixedPoint_mem


theorem stable_exists_unique_fixedPoint
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    ∃! p : Fin W.nStable → ℝ, W.stable.map p = p :=
  W.stable.exists_unique_fixedPoint


theorem finiteContribution_le_finiteBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (a : α) :
    W.S.finiteContribution a ≤ W.finiteBound :=
  finite_le_of_tableUpperBound W.finiteTable a


theorem tailPrefixSum_le_tablePrefixBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailPrefixSum ≤
      (W.finitePrefix.card : ℝ) * W.finiteBound + W.prefixTailBound := by
  simpa [tailPrefixSum, toWitnessPackage, InfiniteTailWitnessPackage.tailPrefixSum,
    InfiniteTailWitnessPackage.ofContributionSplitTailEnvelope,
    ContributionSplit.infiniteTailCertificate_of_tailEnvelope_off_prefix,
    TailSummability.InfiniteTailCertificate.of_tailEnvelope,
    TailSummability.InfiniteTailCertificate.prefixSum] using
    (W.S.total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn
      W.finitePrefix W.tailEnvelope W.additive W.finiteTable
      W.tailEnvelopeOnPrefix W.prefixTailEnvelopeSum_le)


end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
