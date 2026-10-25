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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectVerticalWindingEvent (R : FKRectTorus) : Set R.Configuration :=
  {omega | ∃ x y : R.Vertex, FKRectVerticalWindingWitness R omega x y}

end
end StatMech.FrontierD
