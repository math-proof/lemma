/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part7
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


theorem tailPrefixSum_le_tablePrefixBudget
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.tailPrefixSum ≤ W.tablePrefixBudget := by
  simpa [tablePrefixBudget, tableFiniteBudget] using
    W.tailPrefixSum_le_tablePrefixBound


theorem prefixTailBound_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.prefixTailBound := by
  have hsum_nonneg :
      0 ≤ ∑ a ∈ W.finitePrefix, W.tailEnvelope a := by
    exact Finset.sum_nonneg fun a _ha => W.tailEnvelope_nonneg a
  exact le_trans hsum_nonneg W.prefixTailEnvelopeSum_le


theorem tableTailBound_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tailBound := by
  simpa [tailBudget] using W.tailBudget_nonneg


theorem tablePrefixBudget_nonneg
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    0 ≤ W.tablePrefixBudget :=
  le_trans W.tailPrefixSum_nonneg W.tailPrefixSum_le_tablePrefixBudget


end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
