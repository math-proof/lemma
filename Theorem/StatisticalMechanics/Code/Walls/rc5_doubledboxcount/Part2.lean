/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc5_doubledboxcount.Part2
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


theorem rc5_collapse_dpairsCount :
    dpairsCount rc5_collapseFamily rc5_collapseFamily = 3 := by decide


theorem rc5_collapse_boxDoubled :
    (boxDoubled rc5_collapseFamily rc5_collapseFamily).card = 3 := by
  rw [rc5_doubled_box_count]; exact rc5_collapse_dpairsCount


theorem rc5_collapse_boxFamily :
    (boxFamily rc5_collapseFamily rc5_collapseFamily).card = 2 := by decide


theorem rc5_collapse_strict :
    (boxFamily rc5_collapseFamily rc5_collapseFamily).card
        < dpairsCount rc5_collapseFamily rc5_collapseFamily ∧
      dpairsCount rc5_collapseFamily rc5_collapseFamily
        = (boxDoubled rc5_collapseFamily rc5_collapseFamily).card := by
  refine ⟨?_, ?_⟩
  · rw [rc5_collapse_boxFamily, rc5_collapse_dpairsCount]; norm_num
  · rw [rc5_collapse_dpairsCount, rc5_collapse_boxDoubled]


theorem rc5_dpairsCount_empty_left (ℬ : Finset (Finset α)) :
    dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
  rw [rc5_dpairsCount_eq_card_dpairs]
  simp [rc5_dpairs]


theorem rc5_doubled_box_count_empty_left (ℬ : Finset (Finset α)) :
    (boxDoubled (∅ : Finset (Finset α)) ℬ).card = 0 := by
  rw [rc5_doubled_box_count, rc5_dpairsCount_empty_left]

end StatMech.Walls
