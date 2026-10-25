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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part42
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentBranchSummand_eq_empty_add_inner
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m =
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m +
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
          e0 m := by
  rw [doubledBoxSourceSectorResidualMomentBranchSummand,
    doubledBoxSourceSectorResidualMomentEmptyBranchSummand,
    doubledBoxSourceSectorResidualMomentInnerPairBranchSummand,
    doubledBoxResidualMomentBranchSummand_eq_empty_add_inner]
  ring

end Exact3D
end StatMech
