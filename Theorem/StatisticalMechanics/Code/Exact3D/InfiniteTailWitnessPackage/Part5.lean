/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part6
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


theorem summable_tailContribution
    (W : InfiniteTailWitnessPackage (α := α) M) :
    Summable W.tailContribution := by
  simpa [tailContribution] using W.tailCertificate.summable_weight


theorem summable_tailWeight
    (W : InfiniteTailWitnessPackage (α := α) M) :
    Summable W.tailCertificate.tailWeight :=
  W.tailCertificate.summable_tail


end InfiniteTailWitnessPackage
end Exact3D
end StatMech
