/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc56sandwich.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc57witnessed.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxRecDepth 4000 in

theorem rc57_box_natRes_card :
    (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card = 2 := by
  rw [rc57_Anat, rc57_Bnat]; decide

set_option maxRecDepth 4000 in


theorem rc57_reflInter_natRes_card :
    (rc20_reflInterComp 3 rc57_Anat rc57_Bnat).card = 3 := by
  rw [rc57_Anat, rc57_Bnat]; decide

set_option maxRecDepth 4000 in


theorem rc57_natNbhd_natRes_card :
    (rc57_natNbhd 3 rc57_Anat rc57_Bnat).card = 1 := by
  rw [rc57_natNbhd, rc57_Anat, rc57_Bnat]; decide

set_option maxRecDepth 4000 in


theorem rc57_naturalHall_fails_fin3 :
    (rc57_natNbhd 3 rc57_Anat rc57_Bnat).card
      < (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card := by
  rw [rc57_natNbhd_natRes_card, rc57_box_natRes_card]; norm_num

set_option maxRecDepth 4000 in


theorem rc57_wall_holds_on_natRes :
    (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card
      ≤ (rc20_reflInterComp 3 rc57_Anat rc57_Bnat).card := by
  rw [rc57_box_natRes_card, rc57_reflInter_natRes_card]; norm_num


end StatMech.Walls
