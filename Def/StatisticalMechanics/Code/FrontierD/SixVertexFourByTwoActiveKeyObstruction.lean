/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoActiveObstructionGrade : Nat × Nat :=
  sixVertexHorizontalPairBigrade
    (sixVertexFourByTwoLowArrows.horizontal,
      sixVertexFourByTwoHighArrows.horizontal)

def sixVertexFourByTwoActiveLowCompletion :
    SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero
      sixVertexFourByTwoLowArrows.horizontal :=
  ⟨⟨sixVertexFourByTwoLowArrows.vertical,
      sixVertexFourByTwoLowArrows_ice⟩,
    sixVertexFourByTwoLowArrows_seamCount⟩

def sixVertexFourByTwoActiveHighCompletion :
    SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoHighArrows.horizontal :=
  ⟨⟨sixVertexFourByTwoHighArrows.vertical,
      sixVertexFourByTwoHighArrows_ice⟩,
    sixVertexFourByTwoHighArrows_seamCount⟩

end
end StatMech.FrontierD
