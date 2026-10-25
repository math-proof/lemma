/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


noncomputable def tailCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.tailPrefixSum + W.tailBudget


noncomputable def tailContribution
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    α → ℝ :=
  W.toWitnessPackage.tailContribution


noncomputable def tailTotalTsum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.toWitnessPackage.tailTotalTsum


noncomputable def tailRemainderSum
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.toWitnessPackage.tailRemainderSum

end InfiniteTailMaskedTableWitnessPackage
end Exact3D
end StatMech
