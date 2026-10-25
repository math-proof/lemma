/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Abbrev.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

theorem program_complete_singleton_of_scan_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V) (e : d.graph.edgeFinset)
    (hencode : edgeOfSegment? d s = some e)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit m b) ⟨d, none⟩ = some e.1)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hsource : sources d.graph (ofEdgeFun d.graph m) =
      {(canonicalEdgeSegment d.graph e).1,
        (canonicalEdgeSegment d.graph e).2.1}) :
    program.CompleteEvent d [s] m := by
  constructor
  · simpa [program, encode, hencode, BondwiseSuffixEvent] using hfirst
  · have hterminal :
        canonicalEdgeSegment d.graph e ∈ d.active /\
          sources d.graph (boolCurrent (fluxBitConfig d.graph oddBit m)) =
            {(canonicalEdgeSegment d.graph e).1,
              (canonicalEdgeSegment d.graph e).2.1} := by
      refine ⟨hactive, ?_⟩
      rw [sources_boolCurrent_oddBit]
      exact hsource
    simpa [program, encode, hencode, BondwiseSegmentProgram.TerminalEvent,
      scan, terminal, boolSources, e.2] using hterminal


theorem selectorSpec_fiber_singleton_of_scan_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V) (e : d.graph.edgeFinset)
    (hencode : edgeOfSegment? d s = some e)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit m b) ⟨d, none⟩ = some e.1)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hsource : sources d.graph (ofEdgeFun d.graph m) =
      {(canonicalEdgeSegment d.graph e).1,
        (canonicalEdgeSegment d.graph e).2.1}) :
    ((selectorSpec (V := V)).toPartialSelector).Fiber d [s] m := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_singleton_of_scan_data d m s e hencode hfirst
    hactive hsource


theorem program_complete_canonical_unitFlux
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
    program.CompleteEvent d [canonicalEdgeSegment d.graph e]
      (unitFlux d.graph e) := by
  exact program_complete_singleton_of_scan_data d (unitFlux d.graph e)
    (canonicalEdgeSegment d.graph e) e
    (edgeOfSegment?_canonicalEdgeSegment d e)
    (scan_firstAdmissible_unitFlux d e) hactive
    (sources_unitFlux d.graph e)


theorem program_complete_canonicalEdge
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
    program.CompleteEvent d [canonicalEdgeSegment d.graph e]
      (unitFlux d.graph e) :=
  program_complete_canonical_unitFlux d e hactive


theorem selectorSpec_fiber_canonical_unitFlux
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
    ((selectorSpec (V := V)).toPartialSelector).Fiber d
      [canonicalEdgeSegment d.graph e] (unitFlux d.graph e) := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_canonical_unitFlux d e hactive


theorem concrete_selector_fiber_canonicalEdge
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
    ((completeSpec (V := V)).toPartialSelector).Fiber d
      [canonicalEdgeSegment d.graph e] (unitFlux d.graph e) :=
  selectorSpec_fiber_canonical_unitFlux d e hactive


theorem selectorSpec_fiber_nonempty_is_singleton
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (h : ((selectorSpec (V := V)).toPartialSelector).Fiber
      d (s :: ss) m) :
    ss = [] := by
  have hcomplete :=
    ((selectorSpec (V := V)).fiber_iff_completeEvent d (s :: ss) m).mp h
  rcases program_complete_word_eq_nil_or_singleton d m (s :: ss) hcomplete with
    hnil | ⟨t, hsingleton⟩
  · simp at hnil
  · simpa using congrArg List.tail hsingleton


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
