/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part4


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourCachedGradeCount
    (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ index0 : Fin 16,
    ∑ index1 : Fin 16,
      ∑ index2 : Fin 16,
        ∑ index3 : Fin 16,
          let indices : Fin 4 → Fin 16 := ![index0, index1, index2, index3]
          let vertical : Fin 4 → SixVertexRow 4 := ![
            sixVertexFourRowOfIndex index0,
            sixVertexFourRowOfIndex index1,
            sixVertexFourRowOfIndex index2,
            sixVertexFourRowOfIndex index3]
          if sixVertexUpCount
              (vertical (svFinLast sixVertexFourByFourTorus.height_pos)) =
              sector.val then
            if sixVertexVerticalRowsTotalC
                (T := sixVertexFourByFourTorus) vertical = totalC then
              ∏ j, sixVertexFourHorizontalTransitionCount
                (indices (SixVertexArrows.cyclicPred
                  sixVertexFourByFourTorus.height_pos j))
                (indices j)
            else 0
          else 0

end
end StatMech.FrontierD
