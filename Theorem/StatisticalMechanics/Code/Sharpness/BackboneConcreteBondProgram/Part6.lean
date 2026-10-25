/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Def.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part6
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

@[simp] theorem sourceClass_nil (d : shb_ExplorationDomain V) :
    sourceClass d [] = ∅ := rfl

@[simp] theorem sourceClass_singleton
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    sourceClass d [s] = {s.1, s.2.1} := rfl


theorem program_complete_functional
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word word' : List (shb_ExplorationSegment V))
    (hword : program.CompleteEvent d word m)
    (hword' : program.CompleteEvent d word' m) :
    word = word' := by
  rcases program_complete_word_eq_nil_or_singleton d m word hword with
    rfl | ⟨s, rfl⟩
  · rcases program_complete_word_eq_nil_or_singleton d m word' hword' with
      rfl | ⟨t, rfl⟩
    · rfl
    · have hnil := (program_complete_nil_iff d m).mp hword
      obtain ⟨e, _, _, hsrc⟩ := program_complete_singleton_data d m t hword'
      rw [hnil] at hsrc
      have hmem := congrArg
        (fun U : Finset V => (canonicalEdgeSegment d.graph e).1 ∈ U) hsrc
      simp at hmem
  · rcases program_complete_word_eq_nil_or_singleton d m word' hword' with
      rfl | ⟨t, rfl⟩
    · have hnil := (program_complete_nil_iff d m).mp hword'
      obtain ⟨e, _, _, hsrc⟩ := program_complete_singleton_data d m s hword
      rw [hnil] at hsrc
      have hmem := congrArg
        (fun U : Finset V => (canonicalEdgeSegment d.graph e).1 ∈ U) hsrc
      simp at hmem
    · simpa [program_complete_singleton_injective d m s t hword hword']


theorem sources_eq_sourceClass_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    sources d.graph (ofEdgeFun d.graph m) = sourceClass d word := by
  rcases program_complete_word_eq_nil_or_singleton d m word h with
    rfl | ⟨s, rfl⟩
  · exact (program_complete_nil_iff d m).mp h
  · obtain ⟨e, hes, _, hsrc⟩ :=
      program_complete_singleton_data d m s h
    subst s
    exact hsrc


theorem head_active_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d (s :: ss) m) :
    s ∈ d.active := by
  rcases program_complete_word_eq_nil_or_singleton d m (s :: ss) h with
    hnil | ⟨t, hsingleton⟩
  · simp at hnil
  · have htail : ss = [] := by simpa using congrArg List.tail hsingleton
    subst ss
    obtain ⟨e, hes, hactive, _⟩ :=
      program_complete_singleton_data d m s h
    simpa only [hes] using hactive


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
