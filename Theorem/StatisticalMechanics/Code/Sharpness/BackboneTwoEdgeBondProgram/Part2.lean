/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part2
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

theorem canonicalPairPath_edges
    (G : SimpleGraph V) (e f : G.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f)) :
    (canonicalPairPath G e f hpath).1.edges = [e.1, f.1] := by
  have hjoin : e.1.out.2 = f.1.out.1 := hpath.1
  have hedgeE : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
  have hedgeF : s(f.1.out.1, f.1.out.2) = f.1 := f.1.out_eq
  change [s(e.1.out.1, e.1.out.2),
    s(e.1.out.2, f.1.out.2)] = [e.1, f.1]
  rw [hedgeE, hjoin, hedgeF]


theorem complete_nil_singleton_false
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (hnil : program.CompleteEvent d [] m)
    (hsingle : program.CompleteEvent d [s] m) : False := by
  have hzero := (program_complete_nil_iff d m).mp hnil
  obtain ⟨e, _, _, _, hsource, _⟩ :=
    program_complete_singleton_data d m s hsingle
  rw [hzero] at hsource
  have hmem : (canonicalEdgeSegment d.graph e).1 ∈ (∅ : Finset V) := by
    rw [hsource]
    simp
  simp at hmem


theorem complete_nil_pair_false
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (hnil : program.CompleteEvent d [] m)
    (hpair : program.CompleteEvent d [s, t] m) : False := by
  have hzero := (program_complete_nil_iff d m).mp hnil
  obtain ⟨e, f, _, _, _, _, _, _, _, hpath, hsource⟩ :=
    program_complete_pair_data d m s t hpair
  apply canonicalPair_boundary_ne_empty d.graph e f hpath
  exact hsource.symm.trans hzero


theorem complete_singleton_pair_false
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t u : shb_ExplorationSegment V)
    (hsingle : program.CompleteEvent d [s] m)
    (hpair : program.CompleteEvent d [t, u] m) : False := by
  obtain ⟨e, _, hfirst, _, _, hfinished⟩ :=
    program_complete_singleton_data d m s hsingle
  obtain ⟨f, g, _, _, hfirst', hsecond, _, _, _, _, _⟩ :=
    program_complete_pair_data d m t u hpair
  have hef : e.1 = f.1 := Option.some.inj (hfirst.symm.trans hfirst')
  have hef' : e = f := Subtype.ext hef
  subst f
  rw [hfinished] at hsecond
  simp at hsecond


theorem program_complete_functional
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word word' : List (shb_ExplorationSegment V))
    (hword : program.CompleteEvent d word m)
    (hword' : program.CompleteEvent d word' m) : word = word' := by
  rcases program_complete_word_shape d m word hword with
    hnil | hsingle | hpair
  · subst word
    rcases program_complete_word_shape d m word' hword' with
      hnil' | hsingle' | hpair'
    · exact hnil'.symm
    · obtain ⟨s, rfl⟩ := hsingle'
      exact (complete_nil_singleton_false d m s hword hword').elim
    · obtain ⟨s, t, rfl⟩ := hpair'
      exact (complete_nil_pair_false d m s t hword hword').elim
  · obtain ⟨s, rfl⟩ := hsingle
    rcases program_complete_word_shape d m word' hword' with
      hnil' | hsingle' | hpair'
    · subst word'
      exact (complete_nil_singleton_false d m s hword' hword).elim
    · obtain ⟨t, rfl⟩ := hsingle'
      obtain ⟨e, hse, hfirst, _, _, _⟩ :=
        program_complete_singleton_data d m s hword
      obtain ⟨f, htf, hfirst', _, _, _⟩ :=
        program_complete_singleton_data d m t hword'
      have hef : e.1 = f.1 := Option.some.inj (hfirst.symm.trans hfirst')
      have hef' : e = f := Subtype.ext hef
      subst f
      rw [← hse, ← htf]
    · obtain ⟨t, u, rfl⟩ := hpair'
      exact (complete_singleton_pair_false d m s t u hword hword').elim
  · obtain ⟨s, t, rfl⟩ := hpair
    rcases program_complete_word_shape d m word' hword' with
      hnil' | hsingle' | hpair'
    · subst word'
      exact (complete_nil_pair_false d m s t hword' hword).elim
    · obtain ⟨u, rfl⟩ := hsingle'
      exact (complete_singleton_pair_false d m u s t hword' hword).elim
    · obtain ⟨u, v, rfl⟩ := hpair'
      obtain ⟨e, f, hse, htf, hfirst, hsecond, _, _, _, _, _⟩ :=
        program_complete_pair_data d m s t hword
      obtain ⟨e', f', hue, hvf, hfirst', hsecond', _, _, _, _, _⟩ :=
        program_complete_pair_data d m u v hword'
      have he : e.1 = e'.1 := Option.some.inj (hfirst.symm.trans hfirst')
      have he' : e = e' := Subtype.ext he
      subst e'
      have hf : f.1 = f'.1 := Option.some.inj (hsecond.symm.trans hsecond')
      have hf' : f = f' := Subtype.ext hf
      subst f'
      rw [← hse, ← htf, ← hue, ← hvf]


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
