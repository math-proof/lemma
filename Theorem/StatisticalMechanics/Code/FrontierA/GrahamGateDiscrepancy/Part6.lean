/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part5


namespace StatMech.FrontierA

theorem exists_maximum_relationPartialMatching
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A -> B -> Prop) :
    ∃ matching : RelationPartialMatching r, matching.IsMaximum := by
  classical
  let candidates : Finset (RelationPartialMatching r) := Finset.univ
  have hcandidates : candidates.Nonempty := by
    let emptyMatching : RelationPartialMatching r :=
      ⟨fun _ => none, by simp, by simp⟩
    exact ⟨emptyMatching, by simp [candidates]⟩
  obtain ⟨matching, _hmem, hmax⟩ := candidates.exists_max_image
    (fun candidate => candidate.support.card) hcandidates
  exact ⟨matching, fun other => hmax other (by simp [candidates])⟩


theorem exists_relationPartialMatching_saturating_unmatched
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A -> B -> Prop) :
    ∃ matching : RelationPartialMatching r,
      matching.IsMaximum ∧
        ∀ a, a ∉ matching.support -> ∀ b, r a b ->
          ∃ a', matching.toFun a' = some b := by
  classical
  let candidates : Finset (RelationPartialMatching r) := Finset.univ
  have hcandidates : candidates.Nonempty := by
    let emptyMatching : RelationPartialMatching r :=
      ⟨fun _ => none, by simp, by simp⟩
    exact ⟨emptyMatching, by simp [candidates]⟩
  obtain ⟨matching, _hmem, hmax⟩ := candidates.exists_max_image
    (fun candidate => candidate.support.card) hcandidates
  refine ⟨matching, fun other => hmax other (by simp [candidates]), ?_⟩
  intro a ha b hab
  by_contra hunused
  push Not at hunused
  let extendedFun : A -> Option B := fun x =>
    if x = a then some b else matching.toFun x
  have hextendedRelated : ∀ {x y}, extendedFun x = some y -> r x y := by
    intro x y hxy
    by_cases hx : x = a
    · subst x
      simp only [extendedFun, if_pos] at hxy
      exact Option.some.inj hxy ▸ hab
    · simp only [extendedFun, if_neg hx] at hxy
      exact matching.related hxy
  have hextendedInjective : ∀ {x y z},
      extendedFun x = some z -> extendedFun y = some z -> x = y := by
    intro x y z hx hy
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · exact hya.symm
      · simp only [extendedFun, if_pos, Option.some.injEq] at hx
        simp only [extendedFun, if_neg hya] at hy
        exact False.elim (hunused y (hy.trans (congrArg some hx.symm)))
    · by_cases hya : y = a
      · subst y
        simp only [extendedFun, if_neg hxa] at hx
        simp only [extendedFun, if_pos, Option.some.injEq] at hy
        exact False.elim (hunused x (hx.trans (congrArg some hy.symm)))
      · simp only [extendedFun, if_neg hxa] at hx
        simp only [extendedFun, if_neg hya] at hy
        exact matching.injective_some hx hy
  let extended : RelationPartialMatching r :=
    ⟨extendedFun, hextendedRelated, hextendedInjective⟩
  have hsupport : extended.support = insert a matching.support := by
    ext x
    by_cases hx : x = a
    · subst x
      simp [RelationPartialMatching.mem_support_iff, extended, extendedFun]
    · simp [RelationPartialMatching.mem_support_iff, extended, extendedFun, hx]
  have hcard : extended.support.card = matching.support.card + 1 := by
    rw [hsupport, Finset.card_insert_of_notMem ha]
  have hle := hmax extended (by simp [candidates])
  omega


end StatMech.FrontierA
