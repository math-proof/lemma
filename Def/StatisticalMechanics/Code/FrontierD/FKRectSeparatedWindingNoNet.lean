module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLeftStripNoNet.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeparatedWindingNoNet.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectVerticalRankOneEvent (R : FKRectTorus) : Set R.Configuration :=
  fkRectVerticalWindingEvent R ∩ {omega | ¬ FKRectHasNet R omega}


end
end StatMech.FrontierD
