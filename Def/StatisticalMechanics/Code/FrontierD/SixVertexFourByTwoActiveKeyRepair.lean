module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoActiveCycleMiddleFirstCompletion :
    SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne
      sixVertexFourByTwoCycleMiddleFirst.horizontal :=
  ⟨⟨sixVertexFourByTwoCycleMiddleFirst.vertical,
      sixVertexFourByTwoCycleMiddleFirst_ice⟩,
    sixVertexFourByTwoCycleMiddleFirst_seamCount⟩

def sixVertexFourByTwoActiveCycleMiddleSecondCompletion :
    SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne
      sixVertexFourByTwoCycleMiddleSecond.horizontal :=
  ⟨⟨sixVertexFourByTwoCycleMiddleSecond.vertical,
      sixVertexFourByTwoCycleMiddleSecond_ice⟩,
    sixVertexFourByTwoCycleMiddleSecond_seamCount⟩

end
end StatMech.FrontierD
