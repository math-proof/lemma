/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part4


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexFourByTwoVerticalMaskInSector (sector : Nat) :=
  {verticalMask : Fin 256 //
    sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus
        (sixVertexFourByTwoArrowsOfMasks 0 verticalMask.val)
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = sector}

end
end StatMech.FrontierD
