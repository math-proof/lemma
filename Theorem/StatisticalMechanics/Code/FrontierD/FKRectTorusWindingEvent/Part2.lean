/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNet.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part2


namespace StatMech.FrontierD

noncomputable section

theorem fkRectVerticalCutConnectionEvent_isIncreasing
    (R : FKRectTorus) (x y : R.Vertex) :
    IsIncreasing (fkRectVerticalCutConnectionEvent R x y) := by
  intro omega tau hot hreach
  exact hreach.mono (fkRectVerticalCutGraph_mono R hot)


theorem fkRectVerticalCutConnection_inter_subset_connection
    (R : FKRectTorus) (x y z : R.Vertex) :
    fkRectVerticalCutConnectionEvent R x y ∩
        fkRectVerticalCutConnectionEvent R y z ⊆
      fkRectVerticalCutConnectionEvent R x z := by
  rintro omega ⟨hxy, hyz⟩
  exact hxy.trans hyz


theorem fkRectCriticalVerticalCutConnectionMass_mul_le
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (x y z : R.Vertex) :
    fkRectCriticalEventMass R q
          (fkRectVerticalCutConnectionEvent R x y) *
        fkRectCriticalEventMass R q
          (fkRectVerticalCutConnectionEvent R y z) ≤
      fkRectCriticalEventMass R q
        (fkRectVerticalCutConnectionEvent R x z) := by
  calc
    _ ≤ fkRectCriticalEventMass R q
        (fkRectVerticalCutConnectionEvent R x y ∩
          fkRectVerticalCutConnectionEvent R y z) :=
      fkRectCriticalEventMass_mul_le_inter R hq
        (fkRectVerticalCutConnectionEvent_isIncreasing R x y)
        (fkRectVerticalCutConnectionEvent_isIncreasing R y z)
    _ ≤ fkRectCriticalEventMass R q
        (fkRectVerticalCutConnectionEvent R x z) :=
      fkRectCriticalEventMass_mono R (lt_of_lt_of_le zero_lt_one hq)
        (fkRectVerticalCutConnection_inter_subset_connection R x y z)


end
end StatMech.FrontierD
