/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


theorem fixedPoint_eq (W : InfiniteTailWitnessPackage (α := α) M) :
    W.rgMap.map W.fixedPoint = W.fixedPoint := by
  apply Prod.ext
  · simp [rgMap, fixedPoint]
  · simpa [rgMap, fixedPoint] using W.stable.fixedPoint_isFixed


end InfiniteTailWitnessPackage
end Exact3D
end StatMech
