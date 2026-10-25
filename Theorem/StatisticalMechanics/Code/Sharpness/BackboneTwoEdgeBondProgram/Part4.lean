/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part4
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

theorem program_complete_pair_of_scan_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V) (e f : d.graph.edgeFinset)
    (hencodeS : edgeOfSegment? d s = some e)
    (hencodeT : edgeOfSegment? d t = some f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit m b) ⟨d, []⟩ = some e.1)
    (hsecond : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit m b) ⟨d, [e.1]⟩ = some f.1)
    (hne : e.1 ≠ f.1)
    (hactiveS : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveT : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f))
    (hsource : sources d.graph (ofEdgeFun d.graph m) =
      {(canonicalEdgeSegment d.graph e).1,
          (canonicalEdgeSegment d.graph e).2.1} ∆
        {(canonicalEdgeSegment d.graph f).1,
          (canonicalEdgeSegment d.graph f).2.1}) :
    program.CompleteEvent d [s, t] m := by
  constructor
  · have hselect : scan.Selects
        (fun _ b => fluxBitConfig d.graph
          BackboneConcreteBondProgram.oddBit m b)
        ⟨d, []⟩ [e.1, f.1] := ⟨hfirst, hsecond, trivial⟩
    simpa [program, encode, hencodeS, hencodeT, BondwiseSuffixEvent]
      using hselect
  · have hterminal :
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
      refine ⟨hne, hactiveS, hactiveT, hpath, ?_⟩
      rw [BackboneConcreteBondProgram.sources_boolCurrent_oddBit]
      exact hsource
    simpa [program, encode, hencodeS, hencodeT,
      BondwiseSegmentProgram.TerminalEvent, scan, terminal, boolSources,
      e.2, f.2] using hterminal


theorem selectorSpec_fiber_pair_of_scan_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V) (e f : d.graph.edgeFinset)
    (hencodeS : edgeOfSegment? d s = some e)
    (hencodeT : edgeOfSegment? d t = some f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit m b) ⟨d, []⟩ = some e.1)
    (hsecond : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit m b) ⟨d, [e.1]⟩ = some f.1)
    (hne : e.1 ≠ f.1)
    (hactiveS : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveT : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f))
    (hsource : sources d.graph (ofEdgeFun d.graph m) =
      {(canonicalEdgeSegment d.graph e).1,
          (canonicalEdgeSegment d.graph e).2.1} ∆
        {(canonicalEdgeSegment d.graph f).1,
          (canonicalEdgeSegment d.graph f).2.1}) :
    (selectorSpec (V := V)).toPartialSelector.Fiber d [s, t] m := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_pair_of_scan_data d m s t e f hencodeS hencodeT
    hfirst hsecond hne hactiveS hactiveT hpath hsource


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
