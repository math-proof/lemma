/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part7
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


def with_larger_prefixTailBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
    {prefixTailBound' : ℝ}
    (hle : W.prefixTailBound ≤ prefixTailBound') :
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
  tailBound := W.tailBound
  tailEnvelope := W.tailEnvelope
  total_nonneg := W.total_nonneg
  additive := W.additive
  finiteTable := W.finiteTable
  tailEnvelopeOnPrefix := W.tailEnvelopeOnPrefix
  prefixTailEnvelopeSum_le := le_trans W.prefixTailEnvelopeSum_le hle
  finite_zero_off_prefix := W.finite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := W.tailEnvelope_nonneg_off_prefix
  tail_le_tailEnvelope_off_prefix := W.tail_le_tailEnvelope_off_prefix
  summable_masked_tailEnvelope := W.summable_masked_tailEnvelope
  masked_tailEnvelope_tsum_le := W.masked_tailEnvelope_tsum_le

end InfiniteTailMaskedTableWitnessPackage
end Exact3D
end StatMech
