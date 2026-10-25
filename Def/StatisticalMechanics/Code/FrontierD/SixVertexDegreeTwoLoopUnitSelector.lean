/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoLoopUnitSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoLoopUnitSelector


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHorizontalDegreeTwoLoopUnitSelector_of_not_high
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1.1.1 source.1.1.2.1)
    (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source) :
    SixVertexHorizontalDegreeTwoLoopUnitSelector source :=
  Classical.choice
    (sixVertexHorizontalDegreeTwoLoopUnitSelector_nonempty_of_not_high
      source hdegree hnon)


end
end StatMech.FrontierD
