/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Structure.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


noncomputable def toWitnessPackage
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    InfiniteTailWitnessPackage (α := α) M :=
  InfiniteTailWitnessPackage.ofContributionSplitTailEnvelope
    M W.scale W.thermal_gt_one W.stable W.S W.finitePrefix W.tailEnvelope
    W.total_nonneg W.additive W.finite_zero_off_prefix
    W.tailEnvelope_nonneg W.tail_le_tailEnvelope_off_prefix
    W.summable_tailEnvelope W.tailEnvelope_tsum_le


end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
