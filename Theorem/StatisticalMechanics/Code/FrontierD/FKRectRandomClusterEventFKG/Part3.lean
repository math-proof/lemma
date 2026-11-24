module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
public import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem fkRectTorusConnectionEvent_isIncreasing
    (R : FKRectTorus) (x y : R.Vertex) :
    IsIncreasing (fkRectTorusConnectionEvent R x y) := by
  intro omega tau hot hreach
  exact hreach.mono (fkRectOpenGraph_mono R hot)


end
end StatMech.FrontierD
