/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoStepCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoStepCount


namespace StatMech.FrontierD

def sixVertexFourTwoStepCountNat
    (start finish : Fin 16) (grade : Nat) : Nat :=
  if hgrade : grade < 9 then
    sixVertexFourTwoStepCountTable start finish ⟨grade, hgrade⟩
  else 0

def sixVertexFourDynamicPairGradeCount
    (seam opposite : Fin 16) (totalC : Nat) : Nat :=
  ∑ grade : Fin (totalC + 1),
    sixVertexFourTwoStepCountNat seam opposite grade.val *
      sixVertexFourTwoStepCountNat opposite seam (totalC - grade.val)

def sixVertexFourDynamicSeamGradeCount
    (sector : Fin 5) (totalC : Nat) (seam : Fin 16) : Nat :=
  if sixVertexUpCount (sixVertexFourRowOfIndex seam) = sector.val then
    ∑ opposite : Fin 16,
      sixVertexFourDynamicPairGradeCount seam opposite totalC
  else 0

def sixVertexFourDynamicGradeCount (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ seam : Fin 16,
    sixVertexFourDynamicSeamGradeCount sector totalC seam

end StatMech.FrontierD
