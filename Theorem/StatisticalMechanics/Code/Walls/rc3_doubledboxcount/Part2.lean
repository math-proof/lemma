/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_doubledboxcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc3_doubledboxcount.Part2
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


theorem rc3_collapse_dpairsCount :
    dpairsCount rc3_collapseFamily rc3_collapseFamily = 3 := by decide


theorem rc3_collapse_boxDoubled :
    (boxDoubled rc3_collapseFamily rc3_collapseFamily).card = 3 := by
  rw [rc3_doubled_box_count]; exact rc3_collapse_dpairsCount


theorem rc3_collapse_boxFamily :
    (boxFamily rc3_collapseFamily rc3_collapseFamily).card = 2 := by decide


theorem rc3_collapse_strict :
    (boxFamily rc3_collapseFamily rc3_collapseFamily).card
        < dpairsCount rc3_collapseFamily rc3_collapseFamily ∧
      dpairsCount rc3_collapseFamily rc3_collapseFamily
        = (boxDoubled rc3_collapseFamily rc3_collapseFamily).card := by
  refine ⟨?_, ?_⟩
  · rw [rc3_collapse_boxFamily, rc3_collapse_dpairsCount]; norm_num
  · rw [rc3_collapse_dpairsCount, rc3_collapse_boxDoubled]


theorem rc3_dpairsCount_empty_left (ℬ : Finset (Finset α)) :
    dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
  rw [rc3_dpairsCount_eq_card_dpairs]
  simp [rc3_dpairs]


theorem rc3_doubled_box_count_empty_left (ℬ : Finset (Finset α)) :
    (boxDoubled (∅ : Finset (Finset α)) ℬ).card = 0 := by
  rw [rc3_doubled_box_count, rc3_dpairsCount_empty_left]

end StatMech.Walls
