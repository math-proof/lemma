import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram
open SimpleGraph Finset StatMech StatMech.Sharpness StatMech.Sharpness.BackboneConcreteBondProgram


/--
[oddBit_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma oddBit_eq_true_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {n : Nat} :
-- imply
  oddBit n = true <-> Odd n := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.oddBit_eq_true_iff n

/--
[sources_boolCurrent_oddBit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma sources_boolCurrent_oddBit_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (m : G.edgeFinset -> Nat) :
-- imply
  sources G (boolCurrent (fluxBitConfig G oddBit m)) = sources G (ofEdgeFun G m) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.sources_boolCurrent_oddBit G m

/--
[canonicalEdgeSegment_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma canonicalEdgeSegment_edgeSet_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e : G.edgeFinset} :
-- imply
  (canonicalEdgeSegment G e).edgeSet = {e.1} := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.canonicalEdgeSegment_edgeSet G e

/--
[edgeOfSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma edgeOfSegment_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {e : d.graph.edgeFinset}
-- given
  (h : edgeOfSegment? d s = some e) :
-- imply
  canonicalEdgeSegment d.graph e = s := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.edgeOfSegment d s e h

/--
[program_complete_nil_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_complete_nil_iff d m

/--
[scan_firstAdmissible_ne_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma scan_firstAdmissible_ne_diagonal_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {x : V}
-- given
  (omega : Sym2 V -> Bool) :
-- imply
  scan.firstAdmissible (fun _ e => omega e) ⟨d, none⟩ ≠ some s(x, x) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.scan_firstAdmissible_ne_diagonal d omega x

/--
[find](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma find_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  [DecidableEq A]
  {xs : List A}
  {a : A}
-- given
  (p : A -> Bool)
  (hnodup : xs.Nodup)
  (ha : a ∈ xs)
  (hp : ∀ x, p x = true <-> x = a) :
-- imply
  xs.find? p = some a := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.find xs a p hnodup ha hp

/--
[scan_firstAdmissible_unitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma scan_firstAdmissible_unitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset} :
-- imply
  scan.firstAdmissible (fun _ f => fluxBitConfig d.graph oddBit (unitFlux d.graph e) f) ⟨d, none⟩ = some e.1 := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.scan_firstAdmissible_unitFlux d e

/--
[sources_unitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma sources_unitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e : G.edgeFinset} :
-- imply
  sources G (ofEdgeFun G (unitFlux G e)) = {(canonicalEdgeSegment G e).1, (canonicalEdgeSegment G e).2.1} := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.sources_unitFlux G e

/--
[canonicalEdgeSegment_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma canonicalEdgeSegment_injective_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V} :
-- imply
  Function.Injective (canonicalEdgeSegment G) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.canonicalEdgeSegment_injective G

/--
[edgeOfSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma edgeOfSegment_eq_2
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset} :
-- imply
  edgeOfSegment? d (canonicalEdgeSegment d.graph e) = some e := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.edgeOfSegment d e

/--
[edgeOfSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma edgeOfSegment_eq_3
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset} :
-- imply
  edgeOfSegment? d (canonicalEdgeSegment d.graph e) = some e := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.edgeOfSegment d e

/--
[program_complete_singleton_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma program_complete_singleton_data_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d [s] m) :
-- imply
  ∃ e : d.graph.edgeFinset, canonicalEdgeSegment d.graph e = s /\ canonicalEdgeSegment d.graph e ∈ d.active /\ sources d.graph (ofEdgeFun d.graph m) = {(canonicalEdgeSegment d.graph e).1, (canonicalEdgeSegment d.graph e).2.1} := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_complete_singleton_data d m s h

/--
[program_complete_singleton_data_with_scan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma program_complete_singleton_data_with_scan_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d [s] m) :
-- imply
  ∃ e : d.graph.edgeFinset, scan.firstAdmissible (fun _ f => fluxBitConfig d.graph oddBit m f) ⟨d, none⟩ = some e.1 /\ canonicalEdgeSegment d.graph e = s /\ canonicalEdgeSegment d.graph e ∈ d.active /\ sources d.graph (ofEdgeFun d.graph m) = {(canonicalEdgeSegment d.graph e).1, (canonicalEdgeSegment d.graph e).2.1} := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_complete_singleton_data_with_scan d m s h

/--
[scan_selects_length_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma scan_selects_length_le_one_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {bonds : List (Sym2 V)}
-- given
  (omega : Sym2 V -> Bool)
  (hselect : scan.Selects (fun _ e => omega e) ⟨d, none⟩ bonds) :
-- imply
  bonds.length <= 1 := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.scan_selects_length_le_one d omega bonds hselect

/--
[program_complete_word_eq_nil_or_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma program_complete_word_eq_nil_or_singleton_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d word m) :
-- imply
  word = [] \/ ∃ s, word = [s] := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_complete_word_eq_nil_or_singleton d m word h

/--
[program_complete_cons_tail_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma program_complete_cons_tail_eq_nil_eq
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
  ss = [] := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_complete_cons_tail_eq_nil d m s ss h

/--
[edgeOfSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma edgeOfSegment_eq_4
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d [s] m) :
-- imply
  ∃ e : d.graph.edgeFinset, edgeOfSegment? d s = some e := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.edgeOfSegment d m s h

/--
[program_complete_singleton_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma program_complete_singleton_injective_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hs : program.CompleteEvent d [s] m)
  (ht : program.CompleteEvent d [t] m) :
-- imply
  s = t := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_complete_singleton_injective d m s t hs ht

/--
[sourceClass_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneConcreteBondProgram.sourceClass_nil d

/--
[sourceClass_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma sourceClass_singleton_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V} :
-- imply
  sourceClass d [s] = {s.1, s.2.1} := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.sourceClass_singleton d s

/--
[program_complete_functional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_complete_functional d m word word' hword hword'

/--
[sources_eq_sourceClass_of_program_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneConcreteBondProgram.sources_eq_sourceClass_of_program_complete d m word h

/--
[head_active_of_program_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneConcreteBondProgram.head_active_of_program_complete d m s ss h

/--
[program_complete_singleton_of_scan_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma program_complete_singleton_of_scan_data_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {e : d.graph.edgeFinset}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hencode : edgeOfSegment? d s = some e)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph oddBit m b) ⟨d, none⟩ = some e.1)
  (hactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (hsource : sources d.graph (ofEdgeFun d.graph m) = {(canonicalEdgeSegment d.graph e).1, (canonicalEdgeSegment d.graph e).2.1}) :
-- imply
  program.CompleteEvent d [s] m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_complete_singleton_of_scan_data d m s e hencode hfirst hactive hsource

/--
[selectorSpec_fiber_singleton_of_scan_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma selectorSpec_fiber_singleton_of_scan_data_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {e : d.graph.edgeFinset}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hencode : edgeOfSegment? d s = some e)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph oddBit m b) ⟨d, none⟩ = some e.1)
  (hactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (hsource : sources d.graph (ofEdgeFun d.graph m) = {(canonicalEdgeSegment d.graph e).1, (canonicalEdgeSegment d.graph e).2.1}) :
-- imply
  ((selectorSpec (V := V)).toPartialSelector).Fiber d [s] m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.selectorSpec_fiber_singleton_of_scan_data d m s e hencode hfirst hactive hsource

/--
[program_complete_canonical_unitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma program_complete_canonical_unitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
-- imply
  program.CompleteEvent d [canonicalEdgeSegment d.graph e] (unitFlux d.graph e) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_complete_canonical_unitFlux d e hactive

/--
[program_complete_canonicalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma program_complete_canonicalEdge_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
-- imply
  program.CompleteEvent d [canonicalEdgeSegment d.graph e] (unitFlux d.graph e) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_complete_canonicalEdge d e hactive

/--
[selectorSpec_fiber_canonical_unitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma selectorSpec_fiber_canonical_unitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
-- imply
  ((selectorSpec (V := V)).toPartialSelector).Fiber d [canonicalEdgeSegment d.graph e] (unitFlux d.graph e) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.selectorSpec_fiber_canonical_unitFlux d e hactive

/--
[concrete_selector_fiber_canonicalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma concrete_selector_fiber_canonicalEdge_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
-- imply
  ((completeSpec (V := V)).toPartialSelector).Fiber d [canonicalEdgeSegment d.graph e] (unitFlux d.graph e) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.concrete_selector_fiber_canonicalEdge d e hactive

/--
[selectorSpec_fiber_nonempty_is_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma selectorSpec_fiber_nonempty_is_singleton_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : ((selectorSpec (V := V)).toPartialSelector).Fiber d (s :: ss) m) :
-- imply
  ss = [] := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.selectorSpec_fiber_nonempty_is_singleton d m s ss h

/--
[intendedOneStepRealization_isEmpty_of_noncanonical_chosen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma intendedOneStepRealization_isEmpty_of_noncanonical_chosen_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hsrc : sources d.graph (ofEdgeFun d.graph m) ≠ ∅)
  (hchosen : shb_oneStepChosenSegment d m = some s)
  (hnoncanonical : ∀ e : d.graph.edgeFinset, canonicalEdgeSegment d.graph e ≠ s) :
-- imply
  IsEmpty (IntendedOneStepRealization (V := V)) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.intendedOneStepRealization_isEmpty_of_noncanonical_chosen d m s hsrc hchosen hnoncanonical

/--
[SelectorRealization.programRealizes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma programRealizes_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {S : shb_PartialCurrentDynamicSelector (V := V)}
  {R : SelectorRealization P S} :
-- imply
  ProgramRealizes P S := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.SelectorRealization.programRealizes R

/--
[nonempty_selectorRealization_iff_programRealizes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma nonempty_selectorRealization_iff_programRealizes_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V)) :
-- imply
  Nonempty (SelectorRealization P S) <-> ProgramRealizes P S := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.nonempty_selectorRealization_iff_programRealizes P S

/--
[program_realizes_selectorSpec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma program_realizes_selectorSpec_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  ProgramRealizes (program (V := V)) (selectorSpec (V := V)).toPartialSelector := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_realizes_selectorSpec

/--
[program_not_realizes_of_two_segment_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma program_not_realizes_of_two_segment_fiber_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (m : d.graph.edgeFinset -> Nat)
  (hfiber : S.Fiber d (s :: t :: ss) m) :
-- imply
  ¬ProgramRealizes (program (V := V)) S := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.program_not_realizes_of_two_segment_fiber S d m s t ss hfiber

/--
[selectorSpec_nonempty_canonicalCertificate_iff_toggleExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma selectorSpec_nonempty_canonicalCertificate_iff_toggleExists_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active) :
-- imply
  Nonempty (AsymmetricBondwiseCoordinateCertificate ((program (V := V)).runSpec d (s :: ss)) (residualVacuumRunSpec d s) (activeSegmentRunSpec d s hs) ((program (V := V)).liftedResidualRunSpec d s ss) (selectorSpec (V := V)).toPartialSelector beta J d s ss hs) <-> (selectorSpec (V := V)).CanonicalBondwiseToggleExists beta J d s ss hs := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.selectorSpec_nonempty_canonicalCertificate_iff_toggleExists beta J d s ss hs

/--
[selectorSpec_canonicalToggleExists_of_componentwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean)
-/
@[path]
private lemma selectorSpec_canonicalToggleExists_of_componentwise_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (h : (selectorSpec (V := V)).CanonicalComponentwiseToggleExists beta J d s ss hs) :
-- imply
  (selectorSpec (V := V)).CanonicalBondwiseToggleExists beta J d s ss hs := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteBondProgram.selectorSpec_canonicalToggleExists_of_componentwise beta J d s ss hs h


-- created on 2026-10-23
