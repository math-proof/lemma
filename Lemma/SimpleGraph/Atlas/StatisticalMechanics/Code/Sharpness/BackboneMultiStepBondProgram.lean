import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneMultiStepBondProgram.Part4
open SimpleGraph Finset StatMech StatMech.Sharpness StatMech.Sharpness.BackboneMultiStepBondProgram


/--
[sourceClass_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma sourceClass_nil_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V} :
-- imply
  sourceClass d [] = ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.sourceClass_nil d

/--
[sourceClass_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma sourceClass_pair_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V} :
-- imply
  sourceClass d [s, t] = pairSourceClass s t := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.sourceClass_pair d s t

/--
[IsDesignatedPair.ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma ne_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (h : IsDesignatedPair d e f) :
-- imply
  e.1 ≠ f.1 := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.IsDesignatedPair.ne h

/--
[scan_edgeOrder_initial_of_designated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma scan_edgeOrder_initial_of_designated_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (h : IsDesignatedPair d e f) :
-- imply
  scan.edgeOrder ⟨d, []⟩ = [e.1] := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.scan_edgeOrder_initial_of_designated h

/--
[scan_edgeOrder_second_of_designated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma scan_edgeOrder_second_of_designated_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (h : IsDesignatedPair d e f) :
-- imply
  scan.edgeOrder (scan.advance ⟨d, []⟩ e.1) = [f.1] := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.scan_edgeOrder_second_of_designated h

/--
[sources_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma sources_twoUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset} :
-- imply
  sources G (ofEdgeFun G (twoUnitFlux G e f)) = pairSourceClass (canonicalEdgeSegment G e) (canonicalEdgeSegment G f) := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.sources_twoUnitFlux G e f

/--
[segmentEnds_canonicalEdgeSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma segmentEnds_canonicalEdgeSegment_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e : G.edgeFinset} :
-- imply
  segmentEnds (canonicalEdgeSegment G e) = e.1.toFinset := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.segmentEnds_canonicalEdgeSegment G e

/--
[pairSourceClass_canonicalEdgeSegment_ne_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma pairSourceClass_canonicalEdgeSegment_ne_empty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e.1 ≠ f.1) :
-- imply
  pairSourceClass (canonicalEdgeSegment G e) (canonicalEdgeSegment G f) ≠ ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.pairSourceClass_canonicalEdgeSegment_ne_empty G e f hne

/--
[scan_selects_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma scan_selects_twoUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hpair : IsDesignatedPair d e f) :
-- imply
  scan.Selects (fun _ g => fluxBitConfig d.graph oddBit (twoUnitFlux d.graph e f) g) ⟨d, []⟩ [e.1, f.1] := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.scan_selects_twoUnitFlux hpair

/--
[program_complete_nil_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma program_complete_nil_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  program.CompleteEvent d [] m <-> sources d.graph (ofEdgeFun d.graph m) = ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.program_complete_nil_iff d m

/--
[scan_firstAdmissible_ne_diagonal_initial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma scan_firstAdmissible_ne_diagonal_initial_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {x : V}
-- given
  (omega : Sym2 V -> Bool) :
-- imply
  scan.firstAdmissible (fun _ e => omega e) ⟨d, []⟩ ≠ some s(x, x) := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.scan_firstAdmissible_ne_diagonal_initial d omega x

/--
[encode_pair_of_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma encode_pair_of_edges_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V}
  {e f : d.graph.edgeFinset}
-- given
  (hs : edgeOfSegment? d s = some e)
  (ht : edgeOfSegment? d t = some f)
  (hne : e.1 ≠ f.1) :
-- imply
  encode d [s, t] = [e.1, f.1] := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.encode_pair_of_edges d s t e f hs ht hne

/--
[program_complete_word_eq_nil_or_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma program_complete_word_eq_nil_or_pair_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d word m) :
-- imply
  word = [] ∨ ∃ s t, word = [s, t] := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.program_complete_word_eq_nil_or_pair d m word h

/--
[edgeOfSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma edgeOfSegment_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d [s, t] m) :
-- imply
  ∃ e f : d.graph.edgeFinset, edgeOfSegment? d s = some e ∧ edgeOfSegment? d t = some f ∧ e.1 ≠ f.1 := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.edgeOfSegment d m s t h

/--
[program_complete_pair_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma program_complete_pair_data_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d [s, t] m) :
-- imply
  ∃ e f : d.graph.edgeFinset, e.1 ≠ f.1 ∧ scan.firstAdmissible (fun _ g => fluxBitConfig d.graph oddBit m g) ⟨d, []⟩ = some e.1 ∧ scan.firstAdmissible (fun _ g => fluxBitConfig d.graph oddBit m g) (scan.advance ⟨d, []⟩ e.1) = some f.1 ∧ canonicalEdgeSegment d.graph e = s ∧ canonicalEdgeSegment d.graph f = t ∧ canonicalEdgeSegment d.graph e ∈ d.active ∧ canonicalEdgeSegment d.graph f ∈ d.active ∧ sources d.graph (ofEdgeFun d.graph m) = pairSourceClass (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f) ∧ sources d.graph (ofEdgeFun d.graph m) ≠ ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.program_complete_pair_data d m s t h

/--
[program_complete_functional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma program_complete_functional_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {word word' : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hword : program.CompleteEvent d word m)
  (hword' : program.CompleteEvent d word' m) :
-- imply
  word = word' := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.program_complete_functional d m word word' hword hword'

/--
[sources_eq_sourceClass_of_program_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma sources_eq_sourceClass_of_program_complete_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d word m) :
-- imply
  sources d.graph (ofEdgeFun d.graph m) = sourceClass d word := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.sources_eq_sourceClass_of_program_complete d m word h

/--
[head_active_of_program_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma head_active_of_program_complete_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d (s :: ss) m) :
-- imply
  s ∈ d.active := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.head_active_of_program_complete d m s ss h

/--
[program_realizes_selectorSpec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma program_realizes_selectorSpec_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  ProgramRealizes (program (V := V)) (selectorSpec (V := V)).toPartialSelector := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.program_realizes_selectorSpec

/--
[program_complete_pair_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma program_complete_pair_of_data_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V}
  {e f : d.graph.edgeFinset}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hs : edgeOfSegment? d s = some e)
  (ht : edgeOfSegment? d t = some f)
  (hne : e.1 ≠ f.1)
  (hselect : scan.Selects (fun _ g => fluxBitConfig d.graph oddBit m g) ⟨d, []⟩ [e.1, f.1])
  (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (hfactive : canonicalEdgeSegment d.graph f ∈ d.active)
  (hsources : sources d.graph (ofEdgeFun d.graph m) = pairSourceClass (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f))
  (hnonempty : sources d.graph (ofEdgeFun d.graph m) ≠ ∅) :
-- imply
  program.CompleteEvent d [s, t] m := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.program_complete_pair_of_data d m s t e f hs ht hne hselect heactive hfactive hsources hnonempty

/--
[program_complete_designated_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma program_complete_designated_twoUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hpair : IsDesignatedPair d e f)
  (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  program.CompleteEvent d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] (twoUnitFlux d.graph e f) := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.program_complete_designated_twoUnitFlux d e f hpair heactive hfactive

/--
[selectorSpec_fiber_designated_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma selectorSpec_fiber_designated_twoUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hpair : IsDesignatedPair d e f)
  (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  ((selectorSpec (V := V)).toPartialSelector).Fiber d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] (twoUnitFlux d.graph e f) := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.selectorSpec_fiber_designated_twoUnitFlux d e f hpair heactive hfactive

/--
[selectorSpec_fiber_designated_twoEdgePath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma selectorSpec_fiber_designated_twoEdgePath_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hpair : IsDesignatedPair d e f)
  (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (hfactive : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : (canonicalEdgeSegment d.graph e).2.1 = (canonicalEdgeSegment d.graph f).1) :
-- imply
  ((selectorSpec (V := V)).toPartialSelector).Fiber d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] (twoUnitFlux d.graph e f) ∧ (canonicalEdgeSegment d.graph e).2.1 = (canonicalEdgeSegment d.graph f).1 := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.selectorSpec_fiber_designated_twoEdgePath d e f hpair heactive hfactive hpath

/--
[selectorRealization_designated_pair_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma selectorRealization_designated_pair_fiber_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {S : shb_PartialCurrentDynamicSelector (V := V)}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (R : SelectorRealization (program (V := V)) S)
  (hpair : IsDesignatedPair d e f)
  (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  S.Fiber d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] (twoUnitFlux d.graph e f) := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.selectorRealization_designated_pair_fiber R d e f hpair heactive hfactive

/--
[intendedOneStepRealization_isEmpty_of_designated_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean)
-/
@[path]
private lemma intendedOneStepRealization_isEmpty_of_designated_pair_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hpair : IsDesignatedPair d e f)
  (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  IsEmpty (SelectorRealization (program (V := V)) (shb_oneStepPartialSelector (V := V))) := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.intendedOneStepRealization_isEmpty_of_designated_pair d e f hpair heactive hfactive


-- created on 2026-10-23
