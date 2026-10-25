/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part8
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


def with_larger_finiteBound
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {finiteBound' : ℝ} (hle : W.finiteBound ≤ finiteBound') :
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
  finiteBound := finiteBound'
  prefixTailBound := W.prefixTailBound
  tailBound := W.tailBound
  tailEnvelope := W.tailEnvelope
  total_nonneg := W.total_nonneg
  additive := W.additive
  finiteTable :=
    { covers := W.finiteTable.covers
      sound := W.finiteTable.sound
      intervalUpper_le := fun c hc =>
        le_trans (W.finiteTable.intervalUpper_le c hc) hle }
  tailEnvelopeOnPrefix := W.tailEnvelopeOnPrefix
  prefixTailEnvelopeSum_le := W.prefixTailEnvelopeSum_le
  finite_zero_off_prefix := W.finite_zero_off_prefix
  tailEnvelope_nonneg := W.tailEnvelope_nonneg
  tail_le_tailEnvelope_off_prefix := W.tail_le_tailEnvelope_off_prefix
  summable_tailEnvelope := W.summable_tailEnvelope
  tailEnvelope_tsum_le := W.tailEnvelope_tsum_le

end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
