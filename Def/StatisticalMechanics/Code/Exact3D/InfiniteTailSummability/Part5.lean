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
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace ContributionSplit

variable {α : Type*} [DecidableEq α]


noncomputable def infiniteTailCertificate_of_tailEnvelope_off_prefix
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
    TailSummability.InfiniteTailCertificate α :=
  TailSummability.InfiniteTailCertificate.of_tailEnvelope
    finitePrefix S.totalContribution tailEnvelope htotal_nonneg
    henvelope_nonneg
    (by
      intro a ha
      calc
        S.totalContribution a =
            S.finiteContribution a + S.tailContribution a := hadd a
        _ = S.tailContribution a := by
          rw [hfinite_zero_off_prefix a ha, zero_add]
        _ ≤ tailEnvelope a := htail_le_tailEnvelope a ha)
    hsummable_tailEnvelope htailEnvelope_tsum_le


noncomputable def infiniteTailCertificate_of_masked_tailEnvelope_off_prefix
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
    TailSummability.InfiniteTailCertificate α :=
  TailSummability.InfiniteTailCertificate.of_masked_tailEnvelope
    finitePrefix S.totalContribution tailEnvelope htotal_nonneg
    henvelope_nonneg_off
    (by
      intro a ha
      calc
        S.totalContribution a =
            S.finiteContribution a + S.tailContribution a := hadd a
        _ = S.tailContribution a := by
          rw [hfinite_zero_off_prefix a ha, zero_add]
        _ ≤ tailEnvelope a := htail_le_tailEnvelope a ha)
    hsummable_masked hmasked_tsum_le


end ContributionSplit
end Exact3D
end StatMech
