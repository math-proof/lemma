/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
import Def.StatisticalMechanics.Code.Walls.rc10core.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc10_deficit_incInc_of_bkr (h : rc10_BKRSetFamily) {n : ℕ}
    {A B : Set (ConfigSpace (Fin n))} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    rc5_deficit A B ≤ 0 := by
  rw [rc5_deficit, rc10_card_box_eq A B hA hB, rc10_card_reflInter_eq A B]
  have hbkr := h n (eventFamily A) (eventFamily B) (rc10_isUpperSet_eventFamily hA)
    (rc10_isUpperSet_eventFamily hB)
  have : (#(rc10_boxSupp (eventFamily A) (eventFamily B)) : ℤ)
      ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by exact_mod_cast hbkr
  omega


end StatMech.Walls
