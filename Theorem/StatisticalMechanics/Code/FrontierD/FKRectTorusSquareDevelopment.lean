/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment


namespace StatMech.FrontierD

noncomputable section

theorem fkRectSquareDevelopPoint_fst_sub_snd (p : Int × Int) :
    (fkRectSquareDevelopPoint p).1 -
        (fkRectSquareDevelopPoint p).2 = p.2 := by
  simp [fkRectSquareDevelopPoint]
  omega


theorem fkRectSquareDevelopPoint_snd_add_rowHalf (p : Int × Int) :
    (fkRectSquareDevelopPoint p).2 + p.2 / 2 = p.1 := by
  simp [fkRectSquareDevelopPoint]


theorem fkRectSquareDevelopPoint_injective :
    Function.Injective fkRectSquareDevelopPoint := by
  intro p q hpq
  have hy : p.2 = q.2 := by
    rw [← fkRectSquareDevelopPoint_fst_sub_snd p,
      ← fkRectSquareDevelopPoint_fst_sub_snd q, hpq]
  have hx : p.1 = q.1 := by
    rw [← fkRectSquareDevelopPoint_snd_add_rowHalf p,
      ← fkRectSquareDevelopPoint_snd_add_rowHalf q, hpq, hy]
  exact Prod.ext hx hy


end
end StatMech.FrontierD
