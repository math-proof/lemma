import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part9
open SimpleGraph Finset StatMech StatMech.Sharpness StatMech.Sharpness.BackboneTwoEdgeBondProgram


/--
[program_complete_nil_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.program_complete_nil_iff d m

/--
[scan_firstAdmissible_ne_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  scan.firstAdmissible (fun _ e => omega e) ⟨d, []⟩ ≠ some s(x, x) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.scan_firstAdmissible_ne_diagonal d omega x

/--
[program_complete_singleton_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  ∃ e : d.graph.edgeFinset, canonicalEdgeSegment d.graph e = s /\ scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m b) ⟨d, []⟩ = some e.1 /\ canonicalEdgeSegment d.graph e ∈ d.active /\ sources d.graph (ofEdgeFun d.graph m) = {(canonicalEdgeSegment d.graph e).1, (canonicalEdgeSegment d.graph e).2.1} /\ scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m b) ⟨d, [e.1]⟩ = none := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.program_complete_singleton_data d m s h

/--
[program_complete_pair_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  ∃ e f : d.graph.edgeFinset, canonicalEdgeSegment d.graph e = s /\ canonicalEdgeSegment d.graph f = t /\ scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m b) ⟨d, []⟩ = some e.1 /\ scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m b) ⟨d, [e.1]⟩ = some f.1 /\ e.1 ≠ f.1 /\ canonicalEdgeSegment d.graph e ∈ d.active /\ canonicalEdgeSegment d.graph f ∈ d.active /\ FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f) /\ sources d.graph (ofEdgeFun d.graph m) = {(canonicalEdgeSegment d.graph e).1, (canonicalEdgeSegment d.graph e).2.1} ∆ {(canonicalEdgeSegment d.graph f).1, (canonicalEdgeSegment d.graph f).2.1} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.program_complete_pair_data d m s t h

/--
[program_complete_three_cons_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma program_complete_three_cons_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t u : shb_ExplorationSegment V}
  {rest : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  ¬program.CompleteEvent d (s :: t :: u :: rest) m := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.program_complete_three_cons_false d m s t u rest

/--
[program_complete_word_shape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma program_complete_word_shape_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d word m) :
-- imply
  word = [] \/ (∃ s, word = [s]) \/ (∃ s t, word = [s, t]) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.program_complete_word_shape d m word h

/--
[canonicalEdgeSegment_start_ne_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma canonicalEdgeSegment_start_ne_end_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e : G.edgeFinset} :
-- imply
  (canonicalEdgeSegment G e).1 ≠ (canonicalEdgeSegment G e).2.1 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.canonicalEdgeSegment_start_ne_end G e

/--
[canonicalPair_boundary_ne_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma canonicalPair_boundary_ne_empty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e) (canonicalEdgeSegment G f)) :
-- imply
  {(canonicalEdgeSegment G e).1, (canonicalEdgeSegment G e).2.1} ∆ {(canonicalEdgeSegment G f).1, (canonicalEdgeSegment G f).2.1} ≠ (∅ : Finset V) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.canonicalPair_boundary_ne_empty G e f hpath

/--
[canonicalPairPath_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma canonicalPairPath_edges_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e) (canonicalEdgeSegment G f)) :
-- imply
  (canonicalPairPath G e f hpath).1.edges = [e.1, f.1] := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.canonicalPairPath_edges G e f hpath

/--
[complete_nil_singleton_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma complete_nil_singleton_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hnil : program.CompleteEvent d [] m)
  (hsingle : program.CompleteEvent d [s] m) :
-- imply
  False := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.complete_nil_singleton_false d m s hnil hsingle

/--
[complete_nil_pair_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma complete_nil_pair_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hnil : program.CompleteEvent d [] m)
  (hpair : program.CompleteEvent d [s, t] m) :
-- imply
  False := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.complete_nil_pair_false d m s t hnil hpair

/--
[complete_singleton_pair_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma complete_singleton_pair_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t u : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hsingle : program.CompleteEvent d [s] m)
  (hpair : program.CompleteEvent d [t, u] m) :
-- imply
  False := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.complete_singleton_pair_false d m s t u hsingle hpair

/--
[program_complete_functional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.program_complete_functional d m word word' hword hword'

/--
[sourceClass_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.sourceClass_nil d

/--
[sources_eq_sourceClass_of_program_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.sources_eq_sourceClass_of_program_complete d m word h

/--
[head_active_of_program_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.head_active_of_program_complete d m s ss h

/--
[program_complete_pair_of_scan_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma program_complete_pair_of_scan_data_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V}
  {e f : d.graph.edgeFinset}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hencodeS : edgeOfSegment? d s = some e)
  (hencodeT : edgeOfSegment? d t = some f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m b) ⟨d, []⟩ = some e.1)
  (hsecond : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m b) ⟨d, [e.1]⟩ = some f.1)
  (hne : e.1 ≠ f.1)
  (hactiveS : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveT : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f))
  (hsource : sources d.graph (ofEdgeFun d.graph m) = {(canonicalEdgeSegment d.graph e).1, (canonicalEdgeSegment d.graph e).2.1} ∆ {(canonicalEdgeSegment d.graph f).1, (canonicalEdgeSegment d.graph f).2.1}) :
-- imply
  program.CompleteEvent d [s, t] m := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.program_complete_pair_of_scan_data d m s t e f hencodeS hencodeT hfirst hsecond hne hactiveS hactiveT hpath hsource

/--
[selectorSpec_fiber_pair_of_scan_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma selectorSpec_fiber_pair_of_scan_data_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V}
  {e f : d.graph.edgeFinset}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hencodeS : edgeOfSegment? d s = some e)
  (hencodeT : edgeOfSegment? d t = some f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m b) ⟨d, []⟩ = some e.1)
  (hsecond : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m b) ⟨d, [e.1]⟩ = some f.1)
  (hne : e.1 ≠ f.1)
  (hactiveS : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveT : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f))
  (hsource : sources d.graph (ofEdgeFun d.graph m) = {(canonicalEdgeSegment d.graph e).1, (canonicalEdgeSegment d.graph e).2.1} ∆ {(canonicalEdgeSegment d.graph f).1, (canonicalEdgeSegment d.graph f).2.1}) :
-- imply
  (selectorSpec (V := V)).toPartialSelector.Fiber d [s, t] m := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.selectorSpec_fiber_pair_of_scan_data d m s t e f hencodeS hencodeT hfirst hsecond hne hactiveS hactiveT hpath hsource

/--
[sources_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma sources_twoUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset} :
-- imply
  sources G (ofEdgeFun G (twoUnitFlux G e f)) = {(canonicalEdgeSegment G e).1, (canonicalEdgeSegment G e).2.1} ∆ {(canonicalEdgeSegment G f).1, (canonicalEdgeSegment G f).2.1} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.sources_twoUnitFlux G e f

/--
[find](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  (hp : ∀ x, x ∈ xs -> (p x = true <-> x = a)) :
-- imply
  xs.find? p = some a := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.find xs a p hnodup ha hp

/--
[scan_secondAdmissible_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma scan_secondAdmissible_twoUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b) ⟨d, [e.1]⟩ = some f.1 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.scan_secondAdmissible_twoUnitFlux d e f hne

/--
[program_complete_canonical_pair_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma program_complete_canonical_pair_twoUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  program.CompleteEvent d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] (twoUnitFlux d.graph e f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.program_complete_canonical_pair_twoUnitFlux d e f hne hfirst hactiveE hactiveF hpath

/--
[selectorSpec_fiber_canonical_pair_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma selectorSpec_fiber_canonical_pair_twoUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  (selectorSpec (V := V)).toPartialSelector.Fiber d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] (twoUnitFlux d.graph e f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.selectorSpec_fiber_canonical_pair_twoUnitFlux d e f hne hfirst hactiveE hactiveF hpath

/--
[fin3PathGraph_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3PathGraph_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  fin3PathGraph.edgeFinset = {s((0 : Fin 3), 1), s((1 : Fin 3), 2)} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3PathGraph_edgeFinset

/--
[fin3LeftEdge_ne_rightEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3LeftEdge_ne_rightEdge_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  fin3LeftEdge ≠ fin3RightEdge := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3LeftEdge_ne_rightEdge

/--
[fin3PathDomain_graph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3PathDomain_graph_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  fin3PathDomain.graph = fin3PathGraph := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3PathDomain_graph

/--
[fin3LeftEdge_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3LeftEdge_active_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  canonicalEdgeSegment fin3PathGraph fin3LeftEdge ∈ fin3PathDomain.active := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3LeftEdge_active

/--
[fin3RightEdge_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3RightEdge_active_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  canonicalEdgeSegment fin3PathGraph fin3RightEdge ∈ fin3PathDomain.active := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3RightEdge_active

/--
[fin3_first_scan_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3_first_scan_cases_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  fin3LeftFirst ∨ fin3RightFirst := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3_first_scan_cases

/--
[fin3_first_scan_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3_first_scan_exclusive_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  ¬(fin3LeftFirst ∧ fin3RightFirst) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3_first_scan_exclusive

/--
[fin3LeftEdge_out_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3LeftEdge_out_cases_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  fin3LeftEdge.1.out = ((0 : Fin 3), 1) ∨ fin3LeftEdge.1.out = ((1 : Fin 3), 0) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3LeftEdge_out_cases

/--
[fin3RightEdge_out_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3RightEdge_out_cases_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  fin3RightEdge.1.out = ((1 : Fin 3), 2) ∨ fin3RightEdge.1.out = ((2 : Fin 3), 1) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3RightEdge_out_cases

/--
[fin3_forward_path_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3_forward_path_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  FormsTwoEdgePath (canonicalEdgeSegment fin3PathGraph fin3LeftEdge) (canonicalEdgeSegment fin3PathGraph fin3RightEdge) <-> fin3LeftEdge.1.out = ((0 : Fin 3), 1) /\ fin3RightEdge.1.out = ((1 : Fin 3), 2) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3_forward_path_iff

/--
[fin3_reverse_path_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3_reverse_path_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  FormsTwoEdgePath (canonicalEdgeSegment fin3PathGraph fin3RightEdge) (canonicalEdgeSegment fin3PathGraph fin3LeftEdge) <-> fin3RightEdge.1.out = ((2 : Fin 3), 1) /\ fin3LeftEdge.1.out = ((1 : Fin 3), 0) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3_reverse_path_iff

/--
[fin3_forward_fiber_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3_forward_fiber_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  (selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain [canonicalEdgeSegment fin3PathGraph fin3LeftEdge, canonicalEdgeSegment fin3PathGraph fin3RightEdge] fin3PathFlux <-> fin3LeftFirst /\ FormsTwoEdgePath (canonicalEdgeSegment fin3PathGraph fin3LeftEdge) (canonicalEdgeSegment fin3PathGraph fin3RightEdge) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3_forward_fiber_iff

/--
[fin3_reverse_fiber_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3_reverse_fiber_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  (selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain [canonicalEdgeSegment fin3PathGraph fin3RightEdge, canonicalEdgeSegment fin3PathGraph fin3LeftEdge] fin3PathFlux <-> fin3RightFirst /\ FormsTwoEdgePath (canonicalEdgeSegment fin3PathGraph fin3RightEdge) (canonicalEdgeSegment fin3PathGraph fin3LeftEdge) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3_reverse_fiber_iff

/--
[fin3_twoSegment_fiber_iff_orientation_and_scan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma fin3_twoSegment_fiber_iff_orientation_and_scan_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  ((selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain [canonicalEdgeSegment fin3PathGraph fin3LeftEdge, canonicalEdgeSegment fin3PathGraph fin3RightEdge] fin3PathFlux ∨ (selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain [canonicalEdgeSegment fin3PathGraph fin3RightEdge, canonicalEdgeSegment fin3PathGraph fin3LeftEdge] fin3PathFlux) <-> (fin3LeftFirst /\ fin3LeftEdge.1.out = ((0 : Fin 3), 1) /\ fin3RightEdge.1.out = ((1 : Fin 3), 2)) ∨ (fin3RightFirst /\ fin3RightEdge.1.out = ((2 : Fin 3), 1) /\ fin3LeftEdge.1.out = ((1 : Fin 3), 0)) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.fin3_twoSegment_fiber_iff_orientation_and_scan

/--
[program_realizes_selectorSpec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
-/
@[path]
private lemma program_realizes_selectorSpec_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  ProgramRealizes (program (V := V)) (selectorSpec (V := V)).toPartialSelector := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.program_realizes_selectorSpec

/--
[selectorSpec_nonempty_canonicalCertificate_iff_toggleExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.selectorSpec_nonempty_canonicalCertificate_iff_toggleExists beta J d s ss hs

/--
[selectorSpec_canonicalToggleExists_of_componentwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean)
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
  apply StatMech.Sharpness.BackboneTwoEdgeBondProgram.selectorSpec_canonicalToggleExists_of_componentwise beta J d s ss hs h


-- created on 2026-10-23
