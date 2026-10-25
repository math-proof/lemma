/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneMultiStepBondProgram.Part3
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneMultiStepBondProgram

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneDeterminedCutSwitching

theorem sources_twoUnitFlux (G : SimpleGraph V) (e f : G.edgeFinset) :
    sources G (ofEdgeFun G (twoUnitFlux G e f)) =
      pairSourceClass (canonicalEdgeSegment G e)
        (canonicalEdgeSegment G f) := by
  change sources G
      (ofEdgeFun G (fun g => unitFlux G e g + unitFlux G f g)) = _
  rw [← ofEdgeFun_add, sources_add, sources_unitFlux, sources_unitFlux]
  rfl

theorem segmentEnds_canonicalEdgeSegment
    (G : SimpleGraph V) (e : G.edgeFinset) :
    segmentEnds (canonicalEdgeSegment G e) = e.1.toFinset := by
  change {e.1.out.1, e.1.out.2} = e.1.toFinset
  rw [← Sym2.toFinset_mk_eq]
  exact congrArg Sym2.toFinset e.1.out_eq

theorem pairSourceClass_canonicalEdgeSegment_ne_empty
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e.1 ≠ f.1) :
    pairSourceClass (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f) ≠ ∅ := by
  intro hempty
  rw [pairSourceClass, segmentEnds_canonicalEdgeSegment,
    segmentEnds_canonicalEdgeSegment] at hempty
  have hfin : e.1.toFinset = f.1.toFinset :=
    Finset.symmDiff_eq_empty.mp hempty
  apply hne
  apply Sym2.ext
  intro x
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hfin]


theorem scan_selects_twoUnitFlux
    {d : shb_ExplorationDomain V} {e f : d.graph.edgeFinset}
    (hpair : IsDesignatedPair d e f) :
    scan.Selects
      (fun _ g => fluxBitConfig d.graph oddBit
        (twoUnitFlux d.graph e f) g)
      ⟨d, []⟩ [e.1, f.1] := by
  have hef : e ≠ f := fun h => hpair.ne (congrArg Subtype.val h)
  have hfe : f ≠ e := Ne.symm hef
  have heedge : e.1 ∈ d.graph.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
  have hfedge : f.1 ∈ d.graph.edgeSet := SimpleGraph.mem_edgeFinset.mp f.2
  constructor
  · unfold shb_DynamicEdgeExploration.firstAdmissible
    rw [scan_edgeOrder_initial_of_designated hpair]
    simp [fluxBitConfig, heedge, oddBit, twoUnitFlux, unitFlux, hef]
  · constructor
    · unfold shb_DynamicEdgeExploration.firstAdmissible
      rw [scan_edgeOrder_second_of_designated hpair]
      simp [fluxBitConfig, hfedge, oddBit, twoUnitFlux, unitFlux, hfe]
    · trivial

@[simp] theorem program_complete_nil_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    program.CompleteEvent d [] m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ := by
  change (True ∧ sources d.graph
    (boolCurrent (fluxBitConfig d.graph oddBit m)) = ∅) <-> _
  rw [sources_boolCurrent_oddBit]
  simp


theorem scan_firstAdmissible_ne_diagonal_initial
    (d : shb_ExplorationDomain V) (omega : Sym2 V -> Bool) (x : V) :
    scan.firstAdmissible (fun _ e => omega e) ⟨d, []⟩ ≠ some s(x, x) := by
  intro h
  have hmem := scan.firstAdmissible_mem (fun _ e => omega e)
    ⟨d, []⟩ s(x, x) h
  have hlist : s(x, x) ∈ d.graph.edgeFinset.1.toList :=
    List.mem_of_mem_take hmem
  have hedge : s(x, x) ∈ d.graph.edgeFinset := by
    simpa using hlist
  have hadj : d.graph.Adj x x := by
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
  exact d.graph.loopless.irrefl x hadj

@[simp] theorem encode_pair_of_edges
    (d : shb_ExplorationDomain V) (s t : shb_ExplorationSegment V)
    (e f : d.graph.edgeFinset)
    (hs : edgeOfSegment? d s = some e)
    (ht : edgeOfSegment? d t = some f)
    (hne : e.1 ≠ f.1) :
    encode d [s, t] = [e.1, f.1] := by
  simp [encode, hs, ht, hne]


theorem program_complete_word_eq_nil_or_pair
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    word = [] ∨ ∃ s t, word = [s, t] := by
  cases word with
  | nil => exact Or.inl rfl
  | cons s rest =>
      cases rest with
      | nil =>
          have hfirst : scan.firstAdmissible
              (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, []⟩ =
              some s(s.1, s.1) := by
            simpa [program, encode, BondwiseSuffixEvent] using h.1
          exact (scan_firstAdmissible_ne_diagonal_initial d
            (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
      | cons t tail =>
          cases tail with
          | nil => exact Or.inr ⟨s, t, rfl⟩
          | cons u us =>
              have hfirst : scan.firstAdmissible
                  (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, []⟩ =
                  some s(s.1, s.1) := by
                simpa [program, encode, BondwiseSuffixEvent] using h.1
              exact (scan_firstAdmissible_ne_diagonal_initial d
                (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim


theorem edgeOfSegment?_pair_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s, t] m) :
    ∃ e f : d.graph.edgeFinset,
      edgeOfSegment? d s = some e ∧ edgeOfSegment? d t = some f ∧
        e.1 ≠ f.1 := by
  cases hs : edgeOfSegment? d s with
  | none =>
      have hfirst : scan.firstAdmissible
          (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, []⟩ =
          some s(s.1, s.1) := by
        simpa [program, encode, hs, BondwiseSuffixEvent] using h.1
      exact (scan_firstAdmissible_ne_diagonal_initial d
        (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
  | some e =>
      cases ht : edgeOfSegment? d t with
      | none =>
          have hfirst : scan.firstAdmissible
              (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, []⟩ =
              some s(s.1, s.1) := by
            simpa [program, encode, hs, ht, BondwiseSuffixEvent] using h.1
          exact (scan_firstAdmissible_ne_diagonal_initial d
            (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
      | some f =>
          by_cases hne : e.1 = f.1
          · have hfirst : scan.firstAdmissible
                (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, []⟩ =
                some s(s.1, s.1) := by
              simpa [program, encode, hs, ht, hne,
                BondwiseSuffixEvent] using h.1
            exact (scan_firstAdmissible_ne_diagonal_initial d
              (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
          · exact ⟨e, f, rfl, rfl, hne⟩


theorem program_complete_pair_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s, t] m) :
    ∃ e f : d.graph.edgeFinset,
      e.1 ≠ f.1 ∧
      scan.firstAdmissible
          (fun _ g => fluxBitConfig d.graph oddBit m g) ⟨d, []⟩ =
        some e.1 ∧
      scan.firstAdmissible
          (fun _ g => fluxBitConfig d.graph oddBit m g)
          (scan.advance ⟨d, []⟩ e.1) = some f.1 ∧
      canonicalEdgeSegment d.graph e = s ∧
      canonicalEdgeSegment d.graph f = t ∧
      canonicalEdgeSegment d.graph e ∈ d.active ∧
      canonicalEdgeSegment d.graph f ∈ d.active ∧
      sources d.graph (ofEdgeFun d.graph m) =
        pairSourceClass (canonicalEdgeSegment d.graph e)
          (canonicalEdgeSegment d.graph f) ∧
      sources d.graph (ofEdgeFun d.graph m) ≠ ∅ := by
  obtain ⟨e, f, hs, ht, hne⟩ :=
    edgeOfSegment?_pair_of_program_complete d m s t h
  have hselect : scan.Selects
      (fun _ g => fluxBitConfig d.graph oddBit m g)
      ⟨d, []⟩ [e.1, f.1] := by
    simpa [program, encode_pair_of_edges d s t e f hs ht hne,
      BondwiseSuffixEvent] using h.1
  have hterminal :
      e.1 ≠ f.1 ∧
      canonicalEdgeSegment d.graph e ∈ d.active ∧
      canonicalEdgeSegment d.graph f ∈ d.active ∧
      sources d.graph (boolCurrent (fluxBitConfig d.graph oddBit m)) =
        pairSourceClass (canonicalEdgeSegment d.graph e)
          (canonicalEdgeSegment d.graph f) ∧
      sources d.graph (boolCurrent (fluxBitConfig d.graph oddBit m)) ≠ ∅ := by
    simpa [BondwiseSegmentProgram.TerminalEvent, program,
      encode_pair_of_edges d s t e f hs ht hne,
      scan, terminal, boolSources, e.2, f.2, hne] using h.2
  have hsources : sources d.graph (ofEdgeFun d.graph m) =
      pairSourceClass (canonicalEdgeSegment d.graph e)
        (canonicalEdgeSegment d.graph f) := by
    rw [← sources_boolCurrent_oddBit d.graph m]
    exact hterminal.2.2.2.1
  have hnonempty : sources d.graph (ofEdgeFun d.graph m) ≠ ∅ := by
    rw [← sources_boolCurrent_oddBit d.graph m]
    exact hterminal.2.2.2.2
  exact ⟨e, f, hne, hselect.1, hselect.2.1,
    edgeOfSegment?_eq_some_spec d s e hs,
    edgeOfSegment?_eq_some_spec d t f ht,
    hterminal.2.1, hterminal.2.2.1, hsources, hnonempty⟩


theorem program_complete_functional
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word word' : List (shb_ExplorationSegment V))
    (hword : program.CompleteEvent d word m)
    (hword' : program.CompleteEvent d word' m) :
    word = word' := by
  rcases program_complete_word_eq_nil_or_pair d m word hword with
    rfl | ⟨s, t, rfl⟩
  · rcases program_complete_word_eq_nil_or_pair d m word' hword' with
      rfl | ⟨u, v, rfl⟩
    · rfl
    · have hzero := (program_complete_nil_iff d m).mp hword
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hnonempty⟩ :=
        program_complete_pair_data d m u v hword'
      exact (hnonempty hzero).elim
  · rcases program_complete_word_eq_nil_or_pair d m word' hword' with
      rfl | ⟨u, v, rfl⟩
    · have hzero := (program_complete_nil_iff d m).mp hword'
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hnonempty⟩ :=
        program_complete_pair_data d m s t hword
      exact (hnonempty hzero).elim
    · obtain ⟨e, f, _, hefirst, hfsecond, hse, htf, _, _, _, _⟩ :=
        program_complete_pair_data d m s t hword
      obtain ⟨e', f', _, hefirst', hfsecond', hue', hvf', _, _, _, _⟩ :=
        program_complete_pair_data d m u v hword'
      have heval : e.1 = e'.1 :=
        Option.some.inj (hefirst.symm.trans hefirst')
      have he : e = e' := Subtype.ext heval
      subst e'
      have hfval : f.1 = f'.1 :=
        Option.some.inj (hfsecond.symm.trans hfsecond')
      have hf : f = f' := Subtype.ext hfval
      subst f'
      have hsu : s = u := hse.symm.trans hue'
      have htv : t = v := htf.symm.trans hvf'
      simp [hsu, htv]


theorem sources_eq_sourceClass_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    sources d.graph (ofEdgeFun d.graph m) = sourceClass d word := by
  rcases program_complete_word_eq_nil_or_pair d m word h with
    rfl | ⟨s, t, rfl⟩
  · exact (program_complete_nil_iff d m).mp h
  · obtain ⟨_, _, _, _, _, hse, htf, _, _, hsources, _⟩ :=
      program_complete_pair_data d m s t h
    simpa [sourceClass, hse, htf] using hsources


theorem head_active_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d (s :: ss) m) :
    s ∈ d.active := by
  rcases program_complete_word_eq_nil_or_pair d m (s :: ss) h with
    hnil | ⟨u, v, hpair⟩
  · simp at hnil
  · have hcomplete : program.CompleteEvent d [u, v] m := by
      rw [← hpair]
      exact h
    obtain ⟨_, _, _, _, _, heu, _, heactive, _, _, _⟩ :=
      program_complete_pair_data d m u v hcomplete
    have hsu : s = u := by
      have hheads := congrArg List.head? hpair
      exact Option.some.inj (by simpa using hheads)
    rw [hsu, ← heu]
    exact heactive


end BackboneMultiStepBondProgram
end
end StatMech.Sharpness
