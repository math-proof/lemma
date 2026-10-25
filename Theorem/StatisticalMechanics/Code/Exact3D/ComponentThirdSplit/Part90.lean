/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part95
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment_of_rowSumSchedule
    (remainingShare tailShare :
      ∀ {n : ℕ},
        ℝ → ℝ →
          Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
            FK.boxVerts 3 n → ℝ) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment
      (liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows
        remainingShare tailShare) := by
  intro β _hβpos _hβc
  filter_upwards [] with n
  intro H _hH Ω v _hv
  dsimp only
  intro x _hx
  rfl

end Exact3D
end StatMech
