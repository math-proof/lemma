/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoVerticalMaskInSector
    (sector : Nat) (omega : SixVertexArrows sixVertexFourByTwoTorus)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus omega
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = sector) :
    SixVertexFourByTwoVerticalMaskInSector sector :=
  ⟨sixVertexFourByTwoVerticalMaskFin omega, by
    have hencoded := congrArg
      (fun arrows => sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByTwoTorus arrows
          (svFinLast sixVertexFourByTwoTorus.height_pos)))
      (sixVertexFourByTwoArrowsOf_encodedMasks omega)
    exact hencoded.trans hsector⟩

end
end StatMech.FrontierD
