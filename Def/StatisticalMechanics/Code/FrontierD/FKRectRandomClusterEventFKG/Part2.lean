module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part2


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

def fkRectTorusConnectionEvent (R : FKRectTorus)
    (x y : R.Vertex) : Set R.Configuration :=
  {omega | (fkRectOpenGraph R omega).Reachable x y}

end
end StatMech.FrontierD
