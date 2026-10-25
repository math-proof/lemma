/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoStrandSplit
import Def.StatisticalMechanics.Code.FrontierD.SixVertexCanonicalUnitPrefix.Part2


namespace StatMech.FrontierD

theorem sixVertexCanonicalUnitPrefix_append_suffix
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (hsum : steps.sum = 2) :
    steps.take (sixVertexCanonicalUnitPrefixLength steps hsteps hsum) ++
        sixVertexCanonicalUnitSuffix steps hsteps hsum = steps := by
  exact List.take_append_drop _ _

theorem sixVertexCanonicalUnitSuffix_sum
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (hsum : steps.sum = 2) :
    (sixVertexCanonicalUnitSuffix steps hsteps hsum).sum = 1 := by
  have hsplit := sixVertexCanonicalUnitPrefix_append_suffix
    steps hsteps hsum
  have hprefix := sixVertexCanonicalUnitPrefix_sum steps hsteps hsum
  rw [← hsplit, List.sum_append, hprefix] at hsum
  omega

theorem sixVertexCanonicalUnitPrefix_ne_nil
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (hsum : steps.sum = 2) :
    steps.take
        (sixVertexCanonicalUnitPrefixLength steps hsteps hsum) ≠ [] := by
  intro hnil
  have hprefix := sixVertexCanonicalUnitPrefix_sum steps hsteps hsum
  rw [hnil] at hprefix
  simp at hprefix

theorem sixVertexCanonicalUnitSuffix_ne_nil
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (hsum : steps.sum = 2) :
    sixVertexCanonicalUnitSuffix steps hsteps hsum ≠ [] := by
  intro hnil
  have hsuffix := sixVertexCanonicalUnitSuffix_sum steps hsteps hsum
  rw [hnil] at hsuffix
  simp at hsuffix


theorem exists_item_prefix_map_sum_eq_of_zeroOrUnitSteps
    {Item : Type*} (items : List Item) (step : Item -> Int)
    (hsteps : ∀ item ∈ items,
      step item = 0 \/ step item = 1 \/ step item = -1)
    (target total : Int) (hsum : (items.map step).sum = total)
    (htarget_nonneg : 0 <= target) (htarget_le : target <= total) :
    exists pre suf : List Item,
      items = pre ++ suf /\ (pre.map step).sum = target := by
  induction items generalizing target total with
  | nil =>
      have htarget : target = 0 := by
        simp only [List.map_nil, List.sum_nil] at hsum
        omega
      exact ⟨[], [], rfl, by simp [htarget]⟩
  | cons item items inductionHypothesis =>
      have hitem := hsteps item (by simp)
      have htail : ∀ next ∈ items,
          step next = 0 \/ step next = 1 \/ step next = -1 := by
        intro next hnext
        exact hsteps next (by simp [hnext])
      by_cases htarget : target = 0
      · exact ⟨[], item :: items, by simp, by simp [htarget]⟩
      · have htarget_pos : 0 < target := by omega
        rcases hitem with hitem | hitem | hitem
        · have htailSum : (items.map step).sum = total := by
            simp only [List.map_cons, List.sum_cons, hitem, zero_add] at *
            assumption
          obtain ⟨pre, suf, hsplit, hprefix⟩ :=
            inductionHypothesis htail target total htailSum
              htarget_nonneg htarget_le
          exact ⟨item :: pre, suf, by simp [hsplit],
            by simp [hitem, hprefix]⟩
        · have htailSum : (items.map step).sum = total - 1 := by
            simp only [List.map_cons, List.sum_cons, hitem] at *
            omega
          obtain ⟨pre, suf, hsplit, hprefix⟩ :=
            inductionHypothesis htail (target - 1) (total - 1) htailSum
              (by omega) (by omega)
          exact ⟨item :: pre, suf, by simp [hsplit],
            by simp [hitem, hprefix]⟩
        · have htailSum : (items.map step).sum = total + 1 := by
            simp only [List.map_cons, List.sum_cons, hitem] at *
            omega
          obtain ⟨pre, suf, hsplit, hprefix⟩ :=
            inductionHypothesis htail (target + 1) (total + 1) htailSum
              (by omega) (by omega)
          exact ⟨item :: pre, suf, by simp [hsplit],
            by simp [hitem, hprefix]⟩

theorem exists_item_prefix_length_sum_eq_one
    {Item : Type*} (items : List Item) (step : Item -> Int)
    (hsteps : ∀ item ∈ items,
      step item = 0 \/ step item = 1 \/ step item = -1)
    (hsum : (items.map step).sum = 2) :
    exists cut : Nat, cut <= items.length /\
      ((items.take cut).map step).sum = 1 := by
  obtain ⟨pre, suf, hsplit, hprefix⟩ :=
    exists_item_prefix_map_sum_eq_of_zeroOrUnitSteps
      items step hsteps 1 2 hsum (by norm_num) (by norm_num)
  refine ⟨pre.length, ?_, ?_⟩
  · rw [hsplit, List.length_append]
    omega
  · rw [hsplit, List.take_left]
    exact hprefix


end StatMech.FrontierD
