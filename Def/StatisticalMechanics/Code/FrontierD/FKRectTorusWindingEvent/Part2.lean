module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNet.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectVerticalCutConnectionEvent (R : FKRectTorus)
    (x y : R.Vertex) : Set R.Configuration :=
  {omega | (fkRectVerticalCutGraph R omega).Reachable x y}

end
end StatMech.FrontierD
