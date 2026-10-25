/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc89nested.Part3
import Def.StatisticalMechanics.Code.Walls.rc90self.Part2
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc90_reflCover_self_of_complClosed (A : Finset (ConfigSpace ι))
    (h : rc90_ComplClosed A) : rc90_ReflCover A A := h


theorem rc90_wall_self_complClosed (A : Finset (ConfigSpace ι)) (h : rc90_ComplClosed A) :
    (rc80_disjOccG A A).card ≤ (rc80_reflInterG A A).card :=
  rc90_wall_reflCover A A (rc90_reflCover_self_of_complClosed A h)


theorem rc90_reflInterG_self_eq_of_complClosed (A : Finset (ConfigSpace ι))
    (h : rc90_ComplClosed A) : rc80_reflInterG A A = A :=
  rc90_reflInterG_eq_left_of_cover A A (rc90_reflCover_self_of_complClosed A h)


end StatMech.Walls
