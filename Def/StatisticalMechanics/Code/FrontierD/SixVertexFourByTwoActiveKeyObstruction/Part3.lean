module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part2
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoActiveObstructionToken :
    SixVertexHorizontalActualDeficitTokens sixVertexFourByTwoTorus
      sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoSectorZero
      sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne :=
  ⟨sixVertexFourByTwoActiveObstructionProfile, sixVertexFourByTwoActiveObstructionFiber,
    ⟨0, sixVertexFourByTwoActiveObstructionProfile_deficit_pos⟩⟩

end
end StatMech.FrontierD
