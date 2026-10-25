/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part3
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeBondProgram

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneDeterminedCutSwitching

@[simp] theorem sourceClass_nil (d : shb_ExplorationDomain V) :
    sourceClass d [] = ∅ := rfl


theorem sources_eq_sourceClass_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    sources d.graph (ofEdgeFun d.graph m) = sourceClass d word := by
  rcases program_complete_word_shape d m word h with
    hnil | hsingle | hpair
  · subst word
    exact (program_complete_nil_iff d m).mp h
  · obtain ⟨s, rfl⟩ := hsingle
    obtain ⟨e, hsegment, _, _, hsource, _⟩ :=
      program_complete_singleton_data d m s h
    change sources d.graph (ofEdgeFun d.graph m) = {s.1, s.2.1}
    rw [← hsegment]
    exact hsource
  · obtain ⟨s, t, rfl⟩ := hpair
    obtain ⟨e, f, hsegmentS, hsegmentT, _, _, _, _, _, _, hsource⟩ :=
      program_complete_pair_data d m s t h
    change sources d.graph (ofEdgeFun d.graph m) =
      {s.1, s.2.1} ∆ {t.1, t.2.1}
    rw [← hsegmentS, ← hsegmentT]
    exact hsource


theorem head_active_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d (s :: ss) m) : s ∈ d.active := by
  cases ss with
  | nil =>
      obtain ⟨e, hsegment, _, hactive, _, _⟩ :=
        program_complete_singleton_data d m s h
      simpa only [← hsegment] using hactive
  | cons t rest =>
      cases rest with
      | nil =>
          obtain ⟨e, f, hsegment, _, _, _, _, hactive, _, _, _⟩ :=
            program_complete_pair_data d m s t h
          simpa only [← hsegment] using hactive
      | cons u rest =>
          exact (program_complete_three_cons_false d m s t u rest h).elim


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
