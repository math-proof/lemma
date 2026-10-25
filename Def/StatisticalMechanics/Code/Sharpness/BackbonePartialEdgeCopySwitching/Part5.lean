/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part2
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def shb_oneStepPartialSelector :
    shb_PartialCurrentDynamicSelector (V := V) where
  sourceClass := fun _ word =>
    match word with
    | [s] => {s.1, s.2.1}
    | _ => ∅
  select? := fun d m =>
    if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
    else (shb_oneStepChosenSegment d m).map (fun s => [s])
  sourceClass_nil := by simp
  sources_eq_sourceClass_of_select := by
    intro d m word hword
    by_cases hvac : sources d.graph (ofEdgeFun d.graph m) = ∅
    · change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
        else (shb_oneStepChosenSegment d m).map (fun s => [s])) =
          some word at hword
      rw [if_pos hvac] at hword
      have : ([] : List (shb_ExplorationSegment V)) = word :=
        Option.some.inj hword
      subst word
      exact hvac
    · change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
        else (shb_oneStepChosenSegment d m).map (fun s => [s])) =
          some word at hword
      rw [if_neg hvac] at hword
      cases hs : shb_oneStepChosenSegment d m with
      | none => simp [hs] at hword
      | some s =>
          simp only [hs, Option.map_some, Option.some.injEq] at hword
          subst word
          exact (shb_oneStepCandidate_of_chosen_eq_some d m s hs).choose_spec.1
  select?_eq_some_nil_iff := by
    intro d m
    by_cases hvac : sources d.graph (ofEdgeFun d.graph m) = ∅
    · simp [hvac]
    · change ((if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
        else (shb_oneStepChosenSegment d m).map (fun s => [s])) = some []) <-> _
      rw [if_neg hvac]
      constructor
      · intro h
        cases hs : shb_oneStepChosenSegment d m <;> simp [hs] at h
      · exact fun h => (hvac h).elim
  head_active_of_select := by
    intro d m s ss hword
    by_cases hvac : sources d.graph (ofEdgeFun d.graph m) = ∅
    · simp [hvac] at hword
    · change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
        else (shb_oneStepChosenSegment d m).map (fun t => [t])) =
          some (s :: ss) at hword
      rw [if_neg hvac] at hword
      cases ht : shb_oneStepChosenSegment d m with
      | none => simp [ht] at hword
      | some t =>
          simp only [ht, Option.map_some, Option.some.injEq,
            List.cons.injEq] at hword
          obtain ⟨rfl, rfl⟩ := hword
          exact (shb_oneStepCandidate_of_chosen_eq_some d m t ht).choose


end
end StatMech.Sharpness
