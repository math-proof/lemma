/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


def retarget {κ : Type*} (W : InfiniteTailWitnessPackage (α := α) M)
    (N : CriticalModel κ) : InfiniteTailWitnessPackage (α := α) N where
  nStable := W.nStable
  scale := W.scale
  thermal := W.thermal
  thermal_gt_one := W.thermal_gt_one
  stable := W.stable
  tailCertificate := W.tailCertificate

end InfiniteTailWitnessPackage
end Exact3D
end StatMech
