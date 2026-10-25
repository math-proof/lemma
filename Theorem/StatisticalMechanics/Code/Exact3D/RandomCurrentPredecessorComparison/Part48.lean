/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part46
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxWeightedSelectedCopyTotalPairCardSourcePairBound_of_allComplementTwoBetaMassCap
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hcap : doubledBoxAllComplementTwoBetaMassCap β n w) :
    doubledBoxWeightedSelectedCopyTotalPairCardSourcePairBound β n v w e0 := by
  intro Ω
  exact
    weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_selectedCopySplitBound_of_allComplementTwoBetaMassCap
      (n := n) (v := v) (w := w) hβ Ω e0 hcap

end Exact3D
end StatMech
