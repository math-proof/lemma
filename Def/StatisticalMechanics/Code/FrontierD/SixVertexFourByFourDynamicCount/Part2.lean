/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoStepCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourWeightedConvolution
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourDynamicCount
open Finset


namespace StatMech.FrontierD

def sixVertexFourTwoStepGrade
    (start middle finish : Fin 16) : Nat :=
  sixVertexRowDistance (sixVertexFourRowOfIndex start)
      (sixVertexFourRowOfIndex middle) +
    sixVertexRowDistance (sixVertexFourRowOfIndex middle)
      (sixVertexFourRowOfIndex finish)

def sixVertexFourTwoStepWeight
    (start middle finish : Fin 16) : Nat :=
  sixVertexFourHorizontalTransitionCount start middle *
    sixVertexFourHorizontalTransitionCount middle finish

def sixVertexFourCycleIndexGradeCountExpanded
    (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ seam : Fin 16,
    ∑ opposite : Fin 16,
      ∑ middle0 : Fin 16,
        ∑ middle2 : Fin 16,
          if sixVertexUpCount (sixVertexFourRowOfIndex seam) = sector.val then
            if sixVertexFourTwoStepGrade seam middle0 opposite +
                sixVertexFourTwoStepGrade opposite middle2 seam = totalC then
              sixVertexFourTwoStepWeight seam middle0 opposite *
                sixVertexFourTwoStepWeight opposite middle2 seam
            else 0
          else 0

def sixVertexFourCycleIndexPairGradeCount
    (seam opposite : Fin 16) (totalC : Nat) : Nat :=
  ∑ middle0 : Fin 16, ∑ middle2 : Fin 16,
    if sixVertexFourTwoStepGrade seam middle0 opposite +
        sixVertexFourTwoStepGrade opposite middle2 seam = totalC then
      sixVertexFourTwoStepWeight seam middle0 opposite *
        sixVertexFourTwoStepWeight opposite middle2 seam
    else 0

def sixVertexFourCycleIndexSeamGradeCount
    (sector : Fin 5) (totalC : Nat) (seam : Fin 16) : Nat :=
  if sixVertexUpCount (sixVertexFourRowOfIndex seam) = sector.val then
    ∑ opposite : Fin 16,
      sixVertexFourCycleIndexPairGradeCount seam opposite totalC
  else 0

def sixVertexFourCycleIndexGradeCount
    (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ seam : Fin 16,
    sixVertexFourCycleIndexSeamGradeCount sector totalC seam

end StatMech.FrontierD
