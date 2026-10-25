/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc88twogen.Part2
import Def.StatisticalMechanics.Code.Walls.rc89nested
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc89_inter_setCompl (A : Finset (ConfigSpace ι)) :
    A ∩ rc89_setCompl A = ∅ := by
  unfold rc89_setCompl
  rw [Finset.inter_sdiff_self]


theorem rc89_wall_setcompl (A : Finset (ConfigSpace ι)) :
    (rc80_disjOccG A (rc89_setCompl A)).card ≤ (rc80_reflInterG A (rc89_setCompl A)).card :=
  rc89_wall_disjoint A (rc89_setCompl A) (rc89_inter_setCompl A)


end StatMech.Walls
