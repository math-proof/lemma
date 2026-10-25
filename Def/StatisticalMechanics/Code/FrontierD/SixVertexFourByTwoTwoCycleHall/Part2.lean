/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoSourceFlatArrows (i : Fin 200) :
    SixVertexArrows sixVertexFourByTwoTorus ×
      SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoSourceIndexArrows
    ((finProdFinEquiv (m := 4) (n := 50)).symm i)

def sixVertexFourByTwoTargetFlatArrows (i : Fin 200) :
    SixVertexArrows sixVertexFourByTwoTorus ×
      SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoTargetIndexArrows
    (sixVertexFourByTwoMatchingTable i)


def sixVertexFourByTwoExceptionalFlatIndex (i : Fin 200) : Prop :=
  i.val = 20 \/ i.val = 29 \/ i.val = 170 \/ i.val = 179

end
end StatMech.FrontierD
