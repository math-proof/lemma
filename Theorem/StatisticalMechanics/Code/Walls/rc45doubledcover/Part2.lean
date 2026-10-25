/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc44boxineq.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc45doubledcover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc45_diagonalBox_exceeds_reflInter_fin3 :
    (rc44_reflInterEComp (Finset.univ : Finset (Fin 3)) rc45_Astep rc45_Bstep).card
      < (rc44_famCylBoxEComp {0, 1}
            (rc44_slab0 2 rc45_Astep) (rc44_slab0 2 rc45_Bstep)).card
        + (rc44_famCylBoxEComp {0, 1}
            (rc44_slab1 2 rc45_Astep) (rc44_slab1 2 rc45_Bstep)).card := by
  rw [rc45_Astep, rc45_Bstep, rc44_slab0, rc44_slab0, rc44_slab1, rc44_slab1]
  decide


end StatMech.Walls
