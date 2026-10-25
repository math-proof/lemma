/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
open scoped BigOperators


namespace StatMech

namespace Exact3D

structure InfiniteTailMaskedTableWitnessPackage {ι Case α : Type*}
    [DecidableEq Case] [DecidableEq α] (M : CriticalModel ι) where
  nStable : ℕ
  scale : BlockScale
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable : FiniteStableWitness nStable
  S : ContributionSplit α
  finitePrefix : Finset α
  table : RatInterval.CaseTable Case
  classify : α → Case
  finiteBound : ℝ
  prefixTailBound : ℝ
  tailBound : ℝ
  tailEnvelope : α → ℝ
  total_nonneg : ∀ a, 0 ≤ S.totalContribution a
  additive : S.Additive
  finiteTable :
    FiniteTableUpperBound table classify S.finiteContribution finiteBound
  tailEnvelopeOnPrefix : S.TailEnvelopeOn finitePrefix tailEnvelope
  prefixTailEnvelopeSum_le :
    (∑ a ∈ finitePrefix, tailEnvelope a) ≤ prefixTailBound
  finite_zero_off_prefix :
    ∀ a, a ∉ finitePrefix → S.finiteContribution a = 0
  tailEnvelope_nonneg_off_prefix :
    ∀ a, a ∉ finitePrefix → 0 ≤ tailEnvelope a
  tail_le_tailEnvelope_off_prefix :
    ∀ a, a ∉ finitePrefix → S.tailContribution a ≤ tailEnvelope a
  summable_masked_tailEnvelope :
    Summable (fun a => if a ∈ finitePrefix then 0 else tailEnvelope a)
  masked_tailEnvelope_tsum_le :
    (∑' a, (if a ∈ finitePrefix then 0 else tailEnvelope a)) ≤ tailBound

end Exact3D
end StatMech
