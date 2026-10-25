/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc89nested.Part3
import Def.StatisticalMechanics.Code.Walls.rc90self
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc90_reflInterG_eq_left_of_cover (A B : Finset (ConfigSpace ι))
    (h : rc90_ReflCover A B) : rc80_reflInterG A B = A := by
  apply Finset.Subset.antisymm
  · 
    exact Finset.filter_subset _ _
  · 
    intro a ha
    simp only [rc80_reflInterG, Finset.mem_filter]
    exact ⟨ha, h a ha⟩


theorem rc90_wall_reflCover (A B : Finset (ConfigSpace ι)) (h : rc90_ReflCover A B) :
    (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
  rw [rc90_reflInterG_eq_left_of_cover A B h]
  calc (rc80_disjOccG A B).card
      ≤ (A ∩ B).card := Finset.card_le_card (rc89_disjOccG_subset_inter A B)
    _ ≤ A.card := Finset.card_le_card (Finset.inter_subset_left)


end StatMech.Walls
