/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc93extra.Part2
import Def.StatisticalMechanics.Code.Walls.rc94extra
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc94_inter_subset_reflInterG_symm (A B : Finset (ConfigSpace ι))
    (h : rc94_InterCoverA A B) : A ∩ B ⊆ rc80_reflInterG B A := by
  intro w hw
  simp only [rc80_reflInterG, Finset.mem_filter]
  exact ⟨(Finset.mem_inter.mp hw).2, h w hw⟩


theorem rc94_wall_interCoverA (A B : Finset (ConfigSpace ι)) (h : rc94_InterCoverA A B) :
    (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
  calc (rc80_disjOccG A B).card
      ≤ (A ∩ B).card := Finset.card_le_card (rc89_disjOccG_subset_inter A B)
    _ ≤ (rc80_reflInterG B A).card :=
        Finset.card_le_card (rc94_inter_subset_reflInterG_symm A B h)
    _ = (rc80_reflInterG A B).card := (rc94_reflInterG_card_symm B A)


theorem rc94_interCoverA_of_complClosed (A B : Finset (ConfigSpace ι))
    (h : rc90_ComplClosed A) : rc94_InterCoverA A B :=
  fun w hw => h w (Finset.mem_inter.mp hw).1


end StatMech.Walls
