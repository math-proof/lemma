/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part5
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_oneStepPartialSelector_admissible_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    shb_oneStepPartialSelector.Admissible d m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ ∨
        ∃ s, shb_oneStepCandidate d m s := by
  by_cases hvac : sources d.graph (ofEdgeFun d.graph m) = ∅
  · simp [shb_PartialCurrentDynamicSelector.Admissible,
      shb_oneStepPartialSelector, hvac]
  · rw [or_iff_right hvac]
    constructor
    · rintro ⟨word, hword⟩
      change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
        else (shb_oneStepChosenSegment d m).map (fun s => [s])) =
          some word at hword
      rw [if_neg hvac] at hword
      cases hs : shb_oneStepChosenSegment d m with
      | none => simp [hs] at hword
      | some s =>
          exact ⟨s, shb_oneStepCandidate_of_chosen_eq_some d m s hs⟩
    · rintro ⟨s, hs⟩
      unfold shb_PartialCurrentDynamicSelector.Admissible
      change ∃ word,
        (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
          else (shb_oneStepChosenSegment d m).map (fun t => [t])) = some word
      rw [if_neg hvac]
      unfold shb_oneStepChosenSegment
      rw [dif_pos ⟨s, hs⟩]
      exact ⟨[Classical.choose ⟨s, hs⟩], rfl⟩


end
end StatMech.Sharpness
