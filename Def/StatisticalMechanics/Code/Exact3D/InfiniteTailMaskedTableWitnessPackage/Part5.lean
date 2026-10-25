/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


noncomputable def tableFiniteBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  (W.finitePrefix.card : ℝ) * W.finiteBound


noncomputable def tablePrefixBudget
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.tableFiniteBudget + W.prefixTailBound


noncomputable def tableCertifiedTotalBound
    (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
    ℝ :=
  W.tablePrefixBudget + W.tailBound

end InfiniteTailMaskedTableWitnessPackage
end Exact3D
end StatMech
