/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Def.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace ContributionSplit

variable {α : Type*}


theorem tsum_total_le_prefix_sum_add_tableTailBound
    {Case : Type*} [DecidableEq α] [DecidableEq Case]
    (S : ContributionSplit α) (support finitePrefix : Finset α)
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {finiteBound tailEnvelopeBound : ℝ} (tailEnvelope : α → ℝ)
    (hprefix : finitePrefix ⊆ support)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hnonneg : ∀ a, 0 ≤ S.totalContribution a)
    (hadd : S.Additive)
    (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum :
      (∑ a ∈ support \ finitePrefix, tailEnvelope a) ≤ tailEnvelopeBound) :
    (∑' a, S.totalContribution a) ≤
      (∑ a ∈ finitePrefix, S.totalContribution a) +
        (((support \ finitePrefix).card : ℝ) * finiteBound +
          tailEnvelopeBound) :=
  by
    simpa [finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn] using
      (S.finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
        support finitePrefix tailEnvelope hprefix hzero hnonneg hadd hfinite htail
        htailSum).tsum_le_prefix_sum_add_tailBound


theorem tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    {Case : Type*} [DecidableEq Case]
    (S : ContributionSplit α) (support : Finset α)
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {finiteBound tailBound : ℝ} (tailEnvelope : α → ℝ)
    (hzero : ∀ a, a ∉ support → S.totalContribution a = 0)
    (hadd : S.Additive)
    (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail : S.TailEnvelopeOn support tailEnvelope)
    (htailSum : (∑ a ∈ support, tailEnvelope a) ≤ tailBound) :
    (∑' a, S.totalContribution a) ≤
      (support.card : ℝ) * finiteBound + tailBound := by
  rw [S.tsum_total_eq_sum_of_zero_off_support support hzero]
  exact S.total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn support
    tailEnvelope hadd hfinite htail htailSum

end ContributionSplit
end Exact3D
end StatMech
