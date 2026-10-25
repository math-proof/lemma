/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneMultiStepBondProgram.Part4
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

theorem program_realizes_selectorSpec :
    ProgramRealizes (program (V := V))
      (selectorSpec (V := V)).toPartialSelector :=
  selectorRealization.programRealizes


theorem program_complete_pair_of_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V) (e f : d.graph.edgeFinset)
    (hs : edgeOfSegment? d s = some e)
    (ht : edgeOfSegment? d t = some f)
    (hne : e.1 ≠ f.1)
    (hselect : scan.Selects
      (fun _ g => fluxBitConfig d.graph oddBit m g)
      ⟨d, []⟩ [e.1, f.1])
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active)
    (hsources : sources d.graph (ofEdgeFun d.graph m) =
      pairSourceClass (canonicalEdgeSegment d.graph e)
        (canonicalEdgeSegment d.graph f))
    (hnonempty : sources d.graph (ofEdgeFun d.graph m) ≠ ∅) :
    program.CompleteEvent d [s, t] m := by
  have hboolSources :
      sources d.graph (boolCurrent (fluxBitConfig d.graph oddBit m)) =
        pairSourceClass (canonicalEdgeSegment d.graph e)
          (canonicalEdgeSegment d.graph f) := by
    rw [sources_boolCurrent_oddBit]
    exact hsources
  have hboolNonempty :
      sources d.graph (boolCurrent (fluxBitConfig d.graph oddBit m)) ≠ ∅ := by
    rw [sources_boolCurrent_oddBit]
    exact hnonempty
  constructor
  · simpa [program, encode_pair_of_edges d s t e f hs ht hne,
      BondwiseSuffixEvent] using hselect
  · simpa [BondwiseSegmentProgram.TerminalEvent, program,
      encode_pair_of_edges d s t e f hs ht hne,
      scan, terminal, boolSources, e.2, f.2, hne] using
        ⟨heactive, hfactive, hboolSources, hboolNonempty⟩


theorem program_complete_designated_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (twoUnitFlux d.graph e f) := by
  exact program_complete_pair_of_data d (twoUnitFlux d.graph e f)
    (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f) e f
    (edgeOfSegment?_canonicalEdgeSegment d e)
    (edgeOfSegment?_canonicalEdgeSegment d f)
    hpair.ne (scan_selects_twoUnitFlux hpair) heactive hfactive
    (sources_twoUnitFlux d.graph e f)
    (by
      rw [sources_twoUnitFlux]
      exact pairSourceClass_canonicalEdgeSegment_ne_empty
        d.graph e f hpair.ne)


theorem selectorSpec_fiber_designated_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    ((selectorSpec (V := V)).toPartialSelector).Fiber d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (twoUnitFlux d.graph e f) := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_designated_twoUnitFlux d e f hpair
    heactive hfactive


theorem selectorSpec_fiber_designated_twoEdgePath
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : (canonicalEdgeSegment d.graph e).2.1 =
      (canonicalEdgeSegment d.graph f).1) :
    ((selectorSpec (V := V)).toPartialSelector).Fiber d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (twoUnitFlux d.graph e f) ∧
      (canonicalEdgeSegment d.graph e).2.1 =
        (canonicalEdgeSegment d.graph f).1 :=
  ⟨selectorSpec_fiber_designated_twoUnitFlux d e f hpair
      heactive hfactive, hpath⟩


theorem selectorRealization_designated_pair_fiber
    {S : shb_PartialCurrentDynamicSelector (V := V)}
    (R : SelectorRealization (program (V := V)) S)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    S.Fiber d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (twoUnitFlux d.graph e f) :=
  (R.complete_iff_fiber _ _ _).mp
    (program_complete_designated_twoUnitFlux d e f hpair
      heactive hfactive)


theorem intendedOneStepRealization_isEmpty_of_designated_pair
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    IsEmpty (SelectorRealization (program (V := V))
      (shb_oneStepPartialSelector (V := V))) := by
  constructor
  intro R
  have hfiber := selectorRealization_designated_pair_fiber R d e f hpair
    heactive hfactive
  unfold shb_PartialCurrentDynamicSelector.Fiber at hfiber
  change (if sources d.graph
      (ofEdgeFun d.graph (twoUnitFlux d.graph e f)) = ∅ then some []
    else (shb_oneStepChosenSegment d
      (twoUnitFlux d.graph e f)).map (fun s => [s])) =
      some [canonicalEdgeSegment d.graph e,
        canonicalEdgeSegment d.graph f] at hfiber
  by_cases hvac : sources d.graph
      (ofEdgeFun d.graph (twoUnitFlux d.graph e f)) = ∅
  · simp [hvac] at hfiber
  · rw [if_neg hvac] at hfiber
    cases hchosen : shb_oneStepChosenSegment d
        (twoUnitFlux d.graph e f) <;> simp [hchosen] at hfiber

end BackboneMultiStepBondProgram
end
end StatMech.Sharpness
