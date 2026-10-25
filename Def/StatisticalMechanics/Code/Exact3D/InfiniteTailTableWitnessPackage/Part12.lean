/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part10
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


def with_larger_tailBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {tailBound' : ℝ} (hle : W.tailBound ≤ tailBound') :
    InfiniteTailTableWitnessPackage (Case := Case) (α := α) M where
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
  prefixTailBound := W.prefixTailBound
  tailBound := tailBound'
  tailEnvelope := W.tailEnvelope
  total_nonneg := W.total_nonneg
  additive := W.additive
  finiteTable := W.finiteTable
  tailEnvelopeOnPrefix := W.tailEnvelopeOnPrefix
  prefixTailEnvelopeSum_le := W.prefixTailEnvelopeSum_le
  finite_zero_off_prefix := W.finite_zero_off_prefix
  tailEnvelope_nonneg := W.tailEnvelope_nonneg
  tail_le_tailEnvelope_off_prefix := W.tail_le_tailEnvelope_off_prefix
  summable_tailEnvelope := W.summable_tailEnvelope
  tailEnvelope_tsum_le := le_trans W.tailEnvelope_tsum_le hle

end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
