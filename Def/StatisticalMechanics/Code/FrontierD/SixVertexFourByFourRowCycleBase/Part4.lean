/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexMarkedSectorRowCycleGradeCountExecutable
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (totalC : Nat) : Nat :=
  ∑ vertical : Fin T.height → SixVertexRow T.width,
    if sixVertexUpCount (vertical (svFinLast T.height_pos)) = sector.val then
      if sixVertexVerticalRowsTotalC vertical = totalC then
        ∏ j, sixVertexHorizontalTransitionWitnessCountExecutable vertical j
      else 0
    else 0

def sixVertexFourByFourRowCycleGradeCountExecutable
    (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ row0 : SixVertexRow 4,
    ∑ row1 : SixVertexRow 4,
      ∑ row2 : SixVertexRow 4,
        ∑ row3 : SixVertexRow 4,
          let vertical : Fin 4 → SixVertexRow 4 := ![row0, row1, row2, row3]
          if sixVertexUpCount
              (vertical (svFinLast sixVertexFourByFourTorus.height_pos)) =
              sector.val then
            if sixVertexVerticalRowsTotalC
                (T := sixVertexFourByFourTorus) vertical = totalC then
              ∏ j,
                sixVertexHorizontalTransitionWitnessCountExecutable
                  (T := sixVertexFourByFourTorus) vertical j
            else 0
          else 0

def sixVertexFourByFourTupleGradeCountExecutable
    (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ rows : SixVertexRow 4 × SixVertexRow 4 ×
      SixVertexRow 4 × SixVertexRow 4,
    let vertical := (piFinFourEquiv (SixVertexRow 4)).symm rows
    if sixVertexUpCount
        (vertical (svFinLast sixVertexFourByFourTorus.height_pos)) =
        sector.val then
      if sixVertexVerticalRowsTotalC
          (T := sixVertexFourByFourTorus) vertical = totalC then
        ∏ j, sixVertexHorizontalTransitionWitnessCountExecutable
          (T := sixVertexFourByFourTorus) vertical j
      else 0
    else 0

end
end StatMech.FrontierD
