/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc_doubledboxcount.Part2
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


theorem rc_collapse_dpairsCount :
    dpairsCount collapseFamily collapseFamily = 3 := by decide


theorem rc_collapse_boxDoubled :
    (boxDoubled collapseFamily collapseFamily).card = 3 := by
  rw [rc_card_boxDoubled_eq_dpairsViaInjOn]; exact rc_collapse_dpairsCount


theorem rc_collapse_boxFamily :
    (boxFamily collapseFamily collapseFamily).card = 2 := by decide


theorem rc_collapse_witness :
    (boxFamily collapseFamily collapseFamily).card
      < dpairsCount collapseFamily collapseFamily ∧
    dpairsCount collapseFamily collapseFamily
      = (boxDoubled collapseFamily collapseFamily).card := by
  refine ⟨?_, ?_⟩
  · rw [rc_collapse_boxFamily, rc_collapse_dpairsCount]; norm_num
  · rw [rc_collapse_dpairsCount, rc_collapse_boxDoubled]


theorem rc_dpairsCount_empty_left (ℬ : Finset (Finset α)) :
    dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
  rw [rc_dpairsCount_eq]
  simp [disjointPairs]


theorem rc_doubledBoxCount_empty_left (ℬ : Finset (Finset α)) :
    (boxDoubled (∅ : Finset (Finset α)) ℬ).card = 0 := by
  rw [rc_card_boxDoubled_eq_dpairsViaInjOn, rc_dpairsCount_empty_left]

end StatMech.Walls
