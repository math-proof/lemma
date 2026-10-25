/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc90self.Part4
import Def.StatisticalMechanics.Code.Walls.rc93extra
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc93_inter_subset_reflInterG (A B : Finset (ConfigSpace ι))
    (h : rc93_InterCover A B) : A ∩ B ⊆ rc80_reflInterG A B := by
  intro w hw
  simp only [rc80_reflInterG, Finset.mem_filter]
  exact ⟨(Finset.mem_inter.mp hw).1, h w hw⟩


theorem rc93_disjOccG_subset_reflInterG (A B : Finset (ConfigSpace ι))
    (h : rc93_InterCover A B) : rc80_disjOccG A B ⊆ rc80_reflInterG A B :=
  (rc89_disjOccG_subset_inter A B).trans (rc93_inter_subset_reflInterG A B h)


theorem rc93_wall_interCover (A B : Finset (ConfigSpace ι)) (h : rc93_InterCover A B) :
    (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card :=
  Finset.card_le_card (rc93_disjOccG_subset_reflInterG A B h)


theorem rc93_interCover_of_reflCover (A B : Finset (ConfigSpace ι))
    (h : rc90_ReflCover A B) : rc93_InterCover A B :=
  fun w hw => h w (Finset.mem_inter.mp hw).1


end StatMech.Walls
