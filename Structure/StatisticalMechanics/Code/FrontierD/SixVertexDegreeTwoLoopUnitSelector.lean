/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoLoopUnitSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoLoopUnitSelector


namespace StatMech.FrontierD

public noncomputable section

structure SixVertexHorizontalDegreeTwoLoopUnitSelector
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) where
  hdegree : SixVertexLocallyDegreeTwo source.1.1.1.1 source.1.1.2.1
  component :
    (sixVertexDegreeTwoSynchronizedGraph source.1.1.1.2.1 source.1.1.2.2.1
      hdegree).ConnectedComponent
  charge : sixVertexDegreeTwoSynchronizedComponentCharge
    source.1.1.1.2.1 source.1.1.2.2.1 hdegree component = 1


end
end StatMech.FrontierD
