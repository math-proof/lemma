/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace ContributionSplit

variable {α : Type*} [DecidableEq α]


theorem tsum_total_le_prefixSum_add_tailBound_of_tailEnvelope_off_prefix
    (S : ContributionSplit α) (finitePrefix : Finset α)
    (tailEnvelope : α → ℝ) {tailBound : ℝ}
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_tailEnvelope : Summable tailEnvelope)
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (S.infiniteTailCertificate_of_tailEnvelope_off_prefix
        finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
        henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
        htailEnvelope_tsum_le).prefixSum + tailBound := by
  simpa [infiniteTailCertificate_of_tailEnvelope_off_prefix] using
    (S.infiniteTailCertificate_of_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le).tsum_weight_le_prefixSum_add_tailBound


theorem
    tsum_total_le_prefixSum_add_tailBound_of_masked_tailEnvelope_off_prefix
    (S : ContributionSplit α) (finitePrefix : Finset α)
    (tailEnvelope : α → ℝ) {tailBound : ℝ}
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    (∑' a, S.totalContribution a) ≤
      (S.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix
        finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
        henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
        hmasked_tsum_le).prefixSum + tailBound := by
  simpa [infiniteTailCertificate_of_masked_tailEnvelope_off_prefix] using
    (S.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le).tsum_weight_le_prefixSum_add_tailBound


theorem tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_tailBound
    {β : Type*} (S : ContributionSplit β) (finitePrefix : Finset β)
    {Case : Type*} [DecidableEq Case]
    {T : RatInterval.CaseTable Case} {classify : β → Case}
    {finiteBound prefixTailBound tailBound : ℝ}
    (tailEnvelope : β → ℝ)
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite :
      FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail_on_prefix : S.TailEnvelopeOn finitePrefix tailEnvelope)
    (htailPrefixSum_le :
      (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg : ∀ a, 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_tailEnvelope : Summable tailEnvelope)
    (htailEnvelope_tsum_le : (∑' a, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (finitePrefix.card : ℝ) * finiteBound + prefixTailBound + tailBound := by
  classical
  have hprefix :
      (S.infiniteTailCertificate_of_tailEnvelope_off_prefix
        finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
        henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
        htailEnvelope_tsum_le).prefixSum ≤
          (finitePrefix.card : ℝ) * finiteBound + prefixTailBound := by
    simpa [infiniteTailCertificate_of_tailEnvelope_off_prefix,
      TailSummability.InfiniteTailCertificate.of_tailEnvelope,
      TailSummability.InfiniteTailCertificate.prefixSum] using
      (S.total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn
        finitePrefix tailEnvelope hadd hfinite htail_on_prefix
        htailPrefixSum_le)
  exact le_trans
    (S.tsum_total_le_prefixSum_add_tailBound_of_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg htail_le_tailEnvelope hsummable_tailEnvelope
      htailEnvelope_tsum_le)
    (add_le_add hprefix (le_refl tailBound))


theorem
    tsum_total_le_card_mul_finiteBound_add_prefixTailBound_add_maskedTailBound
    {β : Type*} (S : ContributionSplit β) (finitePrefix : Finset β)
    [DecidableEq β]
    {Case : Type*} [DecidableEq Case]
    {T : RatInterval.CaseTable Case} {classify : β → Case}
    {finiteBound prefixTailBound tailBound : ℝ}
    (tailEnvelope : β → ℝ)
    (htotal_nonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite :
      FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail_on_prefix : S.TailEnvelopeOn finitePrefix tailEnvelope)
    (htailPrefixSum_le :
      (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound)
    (hfinite_zero_off_prefix :
      ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0)
    (henvelope_nonneg_off : ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a)
    (hsummable_masked :
      Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤
        tailBound) :
    (∑' a, S.totalContribution a) ≤
      (finitePrefix.card : ℝ) * finiteBound + prefixTailBound + tailBound := by
  classical
  have hprefix :
      (S.infiniteTailCertificate_of_masked_tailEnvelope_off_prefix
        finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
        henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
        hmasked_tsum_le).prefixSum ≤
          (finitePrefix.card : ℝ) * finiteBound + prefixTailBound := by
    simpa [infiniteTailCertificate_of_masked_tailEnvelope_off_prefix,
      TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope,
      TailSummability.InfiniteTailCertificate.prefixSum] using
      (S.total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn
        finitePrefix tailEnvelope hadd hfinite htail_on_prefix
        htailPrefixSum_le)
  exact le_trans
    (S.tsum_total_le_prefixSum_add_tailBound_of_masked_tailEnvelope_off_prefix
      finitePrefix tailEnvelope htotal_nonneg hadd hfinite_zero_off_prefix
      henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked
      hmasked_tsum_le)
    (add_le_add hprefix (le_refl tailBound))

end ContributionSplit
end Exact3D
end StatMech
