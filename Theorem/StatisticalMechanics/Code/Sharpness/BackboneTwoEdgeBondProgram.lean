/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram
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

@[simp] theorem program_complete_nil_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    program.CompleteEvent d [] m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ := by
  change (True /\ sources d.graph
    (BackboneConcreteBondProgram.boolCurrent
      (fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m)) = ∅) <-> _
  rw [BackboneConcreteBondProgram.sources_boolCurrent_oddBit]
  simp


theorem scan_firstAdmissible_ne_diagonal
    (d : shb_ExplorationDomain V) (omega : Sym2 V -> Bool) (x : V) :
    scan.firstAdmissible (fun _ e => omega e) ⟨d, []⟩ ≠ some s(x, x) := by
  intro h
  have hmem := scan.firstAdmissible_mem (fun _ e => omega e)
    ⟨d, []⟩ s(x, x) h
  have hedge : s(x, x) ∈ d.graph.edgeFinset := by
    simpa [scan] using hmem
  have hadj : d.graph.Adj x x := by
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
  exact d.graph.loopless.irrefl x hadj


theorem program_complete_singleton_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s] m) :
    ∃ e : d.graph.edgeFinset,
      canonicalEdgeSegment d.graph e = s /\
      scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, []⟩ = some e.1 /\
      canonicalEdgeSegment d.graph e ∈ d.active /\
      sources d.graph (ofEdgeFun d.graph m) =
        {(canonicalEdgeSegment d.graph e).1,
          (canonicalEdgeSegment d.graph e).2.1} /\
      scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, [e.1]⟩ = none := by
  unfold BondwiseSegmentProgram.CompleteEvent at h
  cases hedge : edgeOfSegment? d s with
  | none =>
      have hfirst : scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, []⟩ = some s(s.1, s.1) := by
        simpa [program, encode, hedge, BondwiseSuffixEvent] using h.1
      exact (scan_firstAdmissible_ne_diagonal d
        (fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m)
        s.1 hfirst).elim
  | some e =>
      have hfirst : scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, []⟩ = some e.1 := by
        simpa [program, encode, hedge, BondwiseSuffixEvent] using h.1
      have hsegment : canonicalEdgeSegment d.graph e = s :=
        edgeOfSegment?_eq_some_spec d s e hedge
      have hterminal :
          canonicalEdgeSegment d.graph e ∈ d.active /\
          sources d.graph
              (BackboneConcreteBondProgram.boolCurrent
                (fluxBitConfig d.graph
                  BackboneConcreteBondProgram.oddBit m)) =
            {(canonicalEdgeSegment d.graph e).1,
              (canonicalEdgeSegment d.graph e).2.1} /\
          scan.firstAdmissible
              (fun _ b => fluxBitConfig d.graph
                BackboneConcreteBondProgram.oddBit m b)
              ⟨d, [e.1]⟩ = none := by
        simpa [program, encode, hedge,
          BondwiseSegmentProgram.TerminalEvent, scan, terminal, boolSources,
          e.2] using h.2
      refine ⟨e, hsegment, hfirst, hterminal.1, ?_, hterminal.2.2⟩
      rw [← BackboneConcreteBondProgram.sources_boolCurrent_oddBit
        d.graph m]
      exact hterminal.2.1


theorem program_complete_pair_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s, t] m) :
    ∃ e f : d.graph.edgeFinset,
      canonicalEdgeSegment d.graph e = s /\
      canonicalEdgeSegment d.graph f = t /\
      scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, []⟩ = some e.1 /\
      scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, [e.1]⟩ = some f.1 /\
      e.1 ≠ f.1 /\
      canonicalEdgeSegment d.graph e ∈ d.active /\
      canonicalEdgeSegment d.graph f ∈ d.active /\
      FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
        (canonicalEdgeSegment d.graph f) /\
      sources d.graph (ofEdgeFun d.graph m) =
        {(canonicalEdgeSegment d.graph e).1,
          (canonicalEdgeSegment d.graph e).2.1} ∆
        {(canonicalEdgeSegment d.graph f).1,
          (canonicalEdgeSegment d.graph f).2.1} := by
  unfold BondwiseSegmentProgram.CompleteEvent at h
  cases hedgeS : edgeOfSegment? d s with
  | none =>
      have hfirst : scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, []⟩ = some s(s.1, s.1) := by
        simpa [program, encode, hedgeS, BondwiseSuffixEvent] using h.1
      exact (scan_firstAdmissible_ne_diagonal d
        (fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m)
        s.1 hfirst).elim
  | some e =>
      cases hedgeT : edgeOfSegment? d t with
      | none =>
          have hfirst : scan.firstAdmissible
              (fun _ b => fluxBitConfig d.graph
                BackboneConcreteBondProgram.oddBit m b)
              ⟨d, []⟩ = some s(s.1, s.1) := by
            simpa [program, encode, hedgeS, hedgeT, BondwiseSuffixEvent]
              using h.1
          exact (scan_firstAdmissible_ne_diagonal d
            (fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m)
            s.1 hfirst).elim
      | some f =>
          have hselect : scan.Selects
              (fun _ b => fluxBitConfig d.graph
                BackboneConcreteBondProgram.oddBit m b)
              ⟨d, []⟩ [e.1, f.1] := by
            simpa [program, encode, hedgeS, hedgeT, BondwiseSuffixEvent]
              using h.1
          have hsegmentS : canonicalEdgeSegment d.graph e = s :=
            edgeOfSegment?_eq_some_spec d s e hedgeS
          have hsegmentT : canonicalEdgeSegment d.graph f = t :=
            edgeOfSegment?_eq_some_spec d t f hedgeT
          have hterminal :
              e.1 ≠ f.1 /\
              canonicalEdgeSegment d.graph e ∈ d.active /\
              canonicalEdgeSegment d.graph f ∈ d.active /\
              FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
                (canonicalEdgeSegment d.graph f) /\
              sources d.graph
                  (BackboneConcreteBondProgram.boolCurrent
                    (fluxBitConfig d.graph
                      BackboneConcreteBondProgram.oddBit m)) =
                {(canonicalEdgeSegment d.graph e).1,
                  (canonicalEdgeSegment d.graph e).2.1} ∆
                {(canonicalEdgeSegment d.graph f).1,
                  (canonicalEdgeSegment d.graph f).2.1} := by
            simpa [program, encode, hedgeS, hedgeT,
              BondwiseSegmentProgram.TerminalEvent, scan, terminal,
              boolSources, e.2, f.2] using h.2
          refine ⟨e, f, hsegmentS, hsegmentT, hselect.1,
            hselect.2.1, hterminal.1, hterminal.2.1,
            hterminal.2.2.1, hterminal.2.2.2.1, ?_⟩
          rw [← BackboneConcreteBondProgram.sources_boolCurrent_oddBit
            d.graph m]
          exact hterminal.2.2.2.2


theorem program_complete_three_cons_false
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t u : shb_ExplorationSegment V)
    (rest : List (shb_ExplorationSegment V)) :
    ¬program.CompleteEvent d (s :: t :: u :: rest) m := by
  intro h
  unfold BondwiseSegmentProgram.CompleteEvent at h
  have hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit m b)
      ⟨d, []⟩ = some s(s.1, s.1) := by
    simpa [program, encode, BondwiseSuffixEvent] using h.1
  exact scan_firstAdmissible_ne_diagonal d
    (fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m)
    s.1 hfirst


theorem program_complete_word_shape
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    word = [] \/ (∃ s, word = [s]) \/ (∃ s t, word = [s, t]) := by
  cases word with
  | nil => exact Or.inl rfl
  | cons s rest =>
      cases rest with
      | nil => exact Or.inr (Or.inl ⟨s, rfl⟩)
      | cons t rest =>
          cases rest with
          | nil => exact Or.inr (Or.inr ⟨s, t, rfl⟩)
          | cons u rest => exact (program_complete_three_cons_false
              d m s t u rest h).elim


theorem canonicalEdgeSegment_start_ne_end
    (G : SimpleGraph V) (e : G.edgeFinset) :
    (canonicalEdgeSegment G e).1 ≠ (canonicalEdgeSegment G e).2.1 := by
  simp only [canonicalEdgeSegment]
  intro h
  have hedge : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
  apply G.not_isDiag_of_mem_edgeSet hedge
  rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
  exact h


theorem canonicalPair_boundary_ne_empty
    (G : SimpleGraph V) (e f : G.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f)) :
    {(canonicalEdgeSegment G e).1,
        (canonicalEdgeSegment G e).2.1} ∆
      {(canonicalEdgeSegment G f).1,
        (canonicalEdgeSegment G f).2.1} ≠ (∅ : Finset V) := by
  let s := canonicalEdgeSegment G e
  let t := canonicalEdgeSegment G f
  have hsne : s.1 ≠ s.2.1 := canonicalEdgeSegment_start_ne_end G e
  have hnotStart : s.1 ≠ t.1 := by
    intro h
    exact hsne (h.trans hpath.1.symm)
  have houter : s.1 ≠ t.2.1 := hpath.2
  have hmem : s.1 ∈ ({s.1, s.2.1} : Finset V) ∆ {t.1, t.2.1} := by
    rw [Finset.mem_symmDiff]
    exact Or.inl ⟨by simp, by simp [hnotStart, houter]⟩
  intro hempty
  rw [hempty] at hmem
  simp at hmem


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
