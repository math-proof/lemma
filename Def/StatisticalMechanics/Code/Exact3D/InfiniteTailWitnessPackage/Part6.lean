/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


noncomputable def tailPrefixSum
    (W : InfiniteTailWitnessPackage (α := α) M) : ℝ :=
  W.tailCertificate.prefixSum


def tailBudget (W : InfiniteTailWitnessPackage (α := α) M) : ℝ :=
  W.tailCertificate.tailBound


noncomputable def tailCertifiedTotalBound
    (W : InfiniteTailWitnessPackage (α := α) M) : ℝ :=
  W.tailPrefixSum + W.tailBudget


def tailContribution
    (W : InfiniteTailWitnessPackage (α := α) M) : α → ℝ :=
  W.tailCertificate.weight


end InfiniteTailWitnessPackage
end Exact3D
end StatMech
