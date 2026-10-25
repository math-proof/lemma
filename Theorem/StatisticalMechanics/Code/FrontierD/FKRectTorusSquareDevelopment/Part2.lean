/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectSquareUndevelopPoint_developPoint
    (p : Int × Int) :
    fkRectSquareUndevelopPoint (fkRectSquareDevelopPoint p) = p := by
  apply Prod.ext
  · simp [fkRectSquareUndevelopPoint,
      fkRectSquareDevelopPoint_fst_sub_snd]
    exact fkRectSquareDevelopPoint_snd_add_rowHalf p
  · exact fkRectSquareDevelopPoint_fst_sub_snd p

@[simp] theorem fkRectSquareDevelopPoint_undevelopPoint
    (p : Int × Int) :
    fkRectSquareDevelopPoint (fkRectSquareUndevelopPoint p) = p := by
  apply Prod.ext <;>
    simp [fkRectSquareDevelopPoint, fkRectSquareUndevelopPoint] <;>
    omega


end
end StatMech.FrontierD
