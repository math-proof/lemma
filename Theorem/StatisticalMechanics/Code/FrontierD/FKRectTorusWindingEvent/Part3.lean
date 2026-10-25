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
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectVerticalWindingEvent_isIncreasing (R : FKRectTorus) :
    IsIncreasing (fkRectVerticalWindingEvent R) := by
  intro omega tau hot
  rintro ⟨x, y, hadj, hseam, hreach⟩
  exact ⟨x, y, fkRectOpenGraph_mono R hot hadj, hseam,
    hreach.mono (fkRectVerticalCutGraph_mono R hot)⟩


theorem fkRectOpenAdjacency_inter_verticalCutConnection_subset_winding
    (R : FKRectTorus) (x y : R.Vertex)
    (hseam : fkRectCrossesVerticalSeam R s(x, y)) :
    fkRectOpenAdjacencyEvent R x y ∩
        fkRectVerticalCutConnectionEvent R x y ⊆
      fkRectVerticalWindingEvent R := by
  rintro omega ⟨hadj, hreach⟩
  exact ⟨x, y, hadj, hseam, hreach⟩


theorem fkRectCriticalVerticalWindingMass_ge_fixedWitness
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (x y : R.Vertex) (hseam : fkRectCrossesVerticalSeam R s(x, y)) :
    fkRectCriticalEventMass R q (fkRectOpenAdjacencyEvent R x y) *
        fkRectCriticalEventMass R q
          (fkRectVerticalCutConnectionEvent R x y) ≤
      fkRectCriticalEventMass R q (fkRectVerticalWindingEvent R) := by
  calc
    _ ≤ fkRectCriticalEventMass R q
        (fkRectOpenAdjacencyEvent R x y ∩
          fkRectVerticalCutConnectionEvent R x y) :=
      fkRectCriticalEventMass_mul_le_inter R hq
        (fkRectOpenAdjacencyEvent_isIncreasing R x y)
        (fkRectVerticalCutConnectionEvent_isIncreasing R x y)
    _ ≤ fkRectCriticalEventMass R q (fkRectVerticalWindingEvent R) :=
      fkRectCriticalEventMass_mono R (lt_of_lt_of_le zero_lt_one hq)
        (fkRectOpenAdjacency_inter_verticalCutConnection_subset_winding
          R x y hseam)

end
end StatMech.FrontierD
