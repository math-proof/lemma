/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


def with_tailEnvelope_and_budgets
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    (tailEnvelope' : α → ℝ) {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
    (hprefixSum :
      (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
    (henvelope_nonneg_off :
      ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
    (htail_le_tailEnvelope :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
    (hsummable_masked :
      Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
    (hmasked_tsum_le :
      (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤
        tailBound') :
    InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  S := W.S
  finitePrefix := W.finitePrefix
  table := W.table
  classify := W.classify
  finiteBound := W.finiteBound
  prefixTailBound := prefixTailBound'
  tailBound := tailBound'
  tailEnvelope := tailEnvelope'
  total_nonneg := W.total_nonneg
  additive := W.additive
  finiteTable := W.finiteTable
  tailEnvelopeOnPrefix := htailOnPrefix
  prefixTailEnvelopeSum_le := hprefixSum
  finite_zero_off_prefix := W.finite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := henvelope_nonneg_off
  tail_le_tailEnvelope_off_prefix := htail_le_tailEnvelope
  summable_masked_tailEnvelope := hsummable_masked
  masked_tailEnvelope_tsum_le := hmasked_tsum_le


def with_zero_tailEnvelope_and_budgets
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' tailBound' : ℝ}
    (htailOnPrefix :
      W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
    (hprefix_nonneg : 0 ≤ prefixTailBound')
    (htail_nonpos :
      ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
    (htailBound_nonneg : 0 ≤ tailBound') :
    InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M :=
  W.with_tailEnvelope_and_budgets (fun _ => (0 : ℝ))
    htailOnPrefix
    (by simpa using hprefix_nonneg)
    (by intro _ _; simp)
    htail_nonpos
    (by simp)
    (by simpa using htailBound_nonneg)

end InfiniteTailMaskedTableWitnessPackage
end Exact3D
end StatMech
