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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part94
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseSingletonPayment_of_denominatorNonnegativePayment
    {schedule : LiveSingletonOptionShareSchedule}
    (h :
      LiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativePayment
        schedule) :
    LiveSingletonOptionShareScheduleResidualCaseSingletonPayment schedule := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  dsimp only
  intro x hx
  rcases hn H hH Ω v hv x hx with
    ⟨residualShare, residualDenominator, hshare, _hdenomNonneg,
      hpayment⟩
  exact ⟨residualShare, residualDenominator, hshare, hpayment⟩

end Exact3D
end StatMech
