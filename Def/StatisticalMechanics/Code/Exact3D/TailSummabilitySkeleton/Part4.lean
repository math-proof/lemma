/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace ContributionSplit

variable {α : Type*}


noncomputable def finiteSupportCertificate_of_finiteTableUpperBound_and_tailEnvelopeOn
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
    TailSummability.FiniteSupportCertificate α where
  support := support
  finitePrefix := finitePrefix
  finitePrefix_subset_support := hprefix
  weight := S.totalContribution
  envelope := fun a => finiteBound + tailEnvelope a
  tailBound := ((support \ finitePrefix).card : ℝ) * finiteBound + tailEnvelopeBound
  zero_off_support := hzero
  weight_nonneg := hnonneg
  envelope_nonneg_on_tail := by
    intro a ha _haPrefix
    exact le_trans (hnonneg a)
      (S.total_le_finiteBound_add_tailEnvelopeOn support tailEnvelope
        hadd hfinite htail ha)
  weight_le_envelope_on_tail := by
    intro a ha _haPrefix
    exact S.total_le_finiteBound_add_tailEnvelopeOn support tailEnvelope
      hadd hfinite htail ha
  envelope_tail_sum_le := by
    calc
      (∑ a ∈ support \ finitePrefix, (finiteBound + tailEnvelope a)) =
          (∑ _a ∈ support \ finitePrefix, finiteBound) +
            ∑ a ∈ support \ finitePrefix, tailEnvelope a := by
        rw [Finset.sum_add_distrib]
      _ = ((support \ finitePrefix).card : ℝ) * finiteBound +
            ∑ a ∈ support \ finitePrefix, tailEnvelope a := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((support \ finitePrefix).card : ℝ) * finiteBound +
            tailEnvelopeBound := by
        exact add_le_add (le_refl _) htailSum


end ContributionSplit
end Exact3D
end StatMech
