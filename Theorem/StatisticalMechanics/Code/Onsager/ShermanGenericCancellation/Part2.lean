/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanGenericCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanListSeries.Part2
import Theorem.StatisticalMechanics.Code.Onsager.ShermanReroot.Part4
import Def.StatisticalMechanics.Code.Onsager.ShermanGenericCancellation.Part2


namespace StatMech.Onsager

open Matrix BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem listSeriesTerm_eq_zero_of_invalid (Lambda : Matrix E E ℂ) (e r : E)
    (ss : List (List E)) (hbad : ¬ ons_validFactorList e r ss) :
    ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) ss = 0 := by
  classical
  unfold ons_validFactorList at hbad
  push Not at hbad
  obtain ⟨s, hs, hsinvalid⟩ := hbad
  have hinvalid : ¬ (ons_isFirstReturnSegment e s ∧ ∀ x ∈ s, x ≠ r) := by
    rintro ⟨hfirst, havoid⟩
    obtain ⟨x, hx, hxr⟩ := hsinvalid hfirst
    exact havoid x hx hxr
  unfold ons_listSeriesTerm
  split_ifs with hempty
  · rfl
  · apply (div_eq_zero_iff).2
    left
    rw [List.prod_eq_zero_iff]
    exact List.mem_map.mpr ⟨s, hs, by simp [ons_firstReturnWeight, hinvalid]⟩

theorem listSeriesTerm_valid (Lambda : Matrix E E ℂ) (e r : E)
    (ss : List (List E)) (hvalid : ons_validFactorList e r ss) :
    ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) ss =
      if ss = [] then 0 else
        (ss.map (ons_edgeWeight Lambda)).prod / (ss.length : ℂ) := by
  classical
  unfold ons_listSeriesTerm
  by_cases hempty : ss = []
  · simp [hempty]
  · rw [dif_neg hempty, if_neg hempty]
    congr 1
    have hprod : ∀ xs : List (List E), ons_validFactorList e r xs →
        (xs.map (ons_firstReturnWeight Lambda e r)).prod =
          (xs.map (ons_edgeWeight Lambda)).prod := by
      intro xs hxs
      induction xs with
      | nil => rfl
      | cons s xs ih =>
          rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
          have hsvalid := hxs s (by simp)
          rw [show ons_firstReturnWeight Lambda e r s = ons_edgeWeight Lambda s by
            simp only [ons_firstReturnWeight, if_pos hsvalid]]
          congr 1
          apply ih
          intro t ht
          exact hxs t (by simp [ht])
    exact hprod ss hvalid

end StatMech.Onsager
