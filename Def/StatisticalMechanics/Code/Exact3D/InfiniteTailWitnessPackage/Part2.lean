/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Abbrev.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


noncomputable def rgMap (W : InfiniteTailWitnessPackage (α := α) M) :
    BlockSpinMap W.hamiltonian where
  scale := W.scale
  map := fun x => (W.thermal * x.1, W.stable.map x.2)


end InfiniteTailWitnessPackage
end Exact3D
end StatMech
