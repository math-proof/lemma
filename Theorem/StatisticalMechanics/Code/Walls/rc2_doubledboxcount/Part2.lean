/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc2_doubledboxcount.Part2
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


theorem rc2_collapse_dpairsCount :
    dpairsCount rc2_collapseFamily rc2_collapseFamily = 3 := by decide


theorem rc2_collapse_boxDoubled :
    (boxDoubled rc2_collapseFamily rc2_collapseFamily).card = 3 := by
  rw [rc2_doubled_box_count]; exact rc2_collapse_dpairsCount


theorem rc2_collapse_boxFamily :
    (boxFamily rc2_collapseFamily rc2_collapseFamily).card = 2 := by decide


theorem rc2_collapse_witness :
    (boxFamily rc2_collapseFamily rc2_collapseFamily).card
        < dpairsCount rc2_collapseFamily rc2_collapseFamily ∧
      dpairsCount rc2_collapseFamily rc2_collapseFamily
        = (boxDoubled rc2_collapseFamily rc2_collapseFamily).card := by
  refine ⟨?_, ?_⟩
  · rw [rc2_collapse_boxFamily, rc2_collapse_dpairsCount]; norm_num
  · rw [rc2_collapse_dpairsCount, rc2_collapse_boxDoubled]


theorem rc2_dpairsCount_empty_left (ℬ : Finset (Finset α)) :
    dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
  rw [rc2_dpairsCount_eq_card_disjointPairs]
  simp [rc2_disjointPairs]


theorem rc2_doubled_box_count_empty_left (ℬ : Finset (Finset α)) :
    (boxDoubled (∅ : Finset (Finset α)) ℬ).card = 0 := by
  rw [rc2_doubled_box_count, rc2_dpairsCount_empty_left]

end StatMech.Walls
