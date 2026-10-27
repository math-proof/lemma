import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeExhaustiveProgram.Part3
open SimpleGraph Finset StatMech StatMech.Sharpness StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.Cycle


/--
[complete_implies_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma complete_implies_base_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d word m) :
-- imply
  BackboneTwoEdgeBondProgram.program.CompleteEvent d word m := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.complete_implies_base d word m h

/--
[program_complete_nil_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
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
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.program_complete_nil_iff d m

/--
[program_complete_singleton_iff_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma program_complete_singleton_iff_base_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  program.CompleteEvent d [s] m <-> BackboneTwoEdgeBondProgram.program.CompleteEvent d [s] m := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.program_complete_singleton_iff_base d s m

/--
[program_complete_functional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
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
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.program_complete_functional d m word word' hword hword'

/--
[sources_eq_sourceClass_of_program_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
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
  sources d.graph (ofEdgeFun d.graph m) = BackboneTwoEdgeBondProgram.sourceClass d word := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.sources_eq_sourceClass_of_program_complete d m word h

/--
[head_active_of_program_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
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
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.head_active_of_program_complete d m s ss h

/--
[noFurtherOdd_twoUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma noFurtherOdd_twoUnit_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset} :
-- imply
  NoFurtherOdd ⟨d, [e.1, f.1]⟩ e.1 f.1 (fluxBitConfig d.graph oddBit (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.noFurtherOdd_twoUnit d e f

/--
[program_complete_canonical_pair_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
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
  (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible (fun _ b => fluxBitConfig d.graph oddBit (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  program.CompleteEvent d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.program_complete_canonical_pair_twoUnitFlux d e f hne hfirst hactiveE hactiveF hpath

/--
[selectorSpec_fiber_canonical_pair_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
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
  (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible (fun _ b => fluxBitConfig d.graph oddBit (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  (selectorSpec (V := V)).toPartialSelector.Fiber d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.selectorSpec_fiber_canonical_pair_twoUnitFlux d e f hne hfirst hactiveE hactiveF hpath

/--
[noFurtherOdd_of_complete_canonical_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma noFurtherOdd_of_complete_canonical_pair_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : program.CompleteEvent d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] m) :
-- imply
  NoFurtherOdd (⟨d, [e.1, f.1]⟩ : BackboneTwoEdgeBondProgram.State V) e.1 f.1 (fluxBitConfig d.graph oddBit m) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.noFurtherOdd_of_complete_canonical_pair d e f m h

/--
[runSpec_singleton_event_iff_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma runSpec_singleton_event_iff_base_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  ((program (V := V)).runSpec d [s]).Event d.graph m <-> ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d [s]).Event d.graph m := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.runSpec_singleton_event_iff_base d s m

/--
[liftedResidualRunSpec_singleton_event_iff_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma liftedResidualRunSpec_singleton_event_iff_base_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s t : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  ((program (V := V)).liftedResidualRunSpec d s [t]).Event d.graph m <-> ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d s [t]).Event d.graph m := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.liftedResidualRunSpec_singleton_event_iff_base d s t m

/--
[fullRun_activeHead_twoUnit_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma fullRun_activeHead_twoUnit_covariance_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible (fun _ b => fluxBitConfig d.graph oddBit (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  BondwiseRunToggleCovariance ((program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE) d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.fullRun_activeHead_twoUnit_covariance d e f hne hfirst hactiveE hactiveF hpath

/--
[residualVacuum_suffix_twoUnit_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma residualVacuum_suffix_twoUnit_covariance_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  BondwiseRunToggleCovariance (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) ((program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.residualVacuum_suffix_twoUnit_covariance d e f hne hactiveF

/--
[twoUnit_componentwise_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma twoUnit_componentwise_covariance_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible (fun _ b => fluxBitConfig d.graph oddBit (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  BondwiseRunToggleCovariance ((program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE) d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} /\ BondwiseRunToggleCovariance (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) ((program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.twoUnit_componentwise_covariance d e f hne hfirst hactiveE hactiveF hpath

/--
[twoUnit_pair_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma twoUnit_pair_toggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
  {T : Finset (Copy d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f))}
-- given
  (hne : e ≠ f)
  (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible (fun _ b => fluxBitConfig d.graph oddBit (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  BondwisePairEvent ((program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) T <-> BondwisePairEvent (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE) ((program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) (T ∆ {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne}) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.twoUnit_pair_toggle d e f hne hfirst hactiveE hactiveF hpath T

/--
[oddTrianglePairFlux_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma oddTrianglePairFlux_cycle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  oddTrianglePairFlux cycleEdge₀ = 1 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.Cycle.oddTrianglePairFlux_cycle

/--
[oddTrianglePairBit_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma oddTrianglePairBit_cycle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  fluxBitConfig domain.graph oddBit oddTrianglePairFlux cycleEdge₀.1 = true := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.Cycle.oddTrianglePairBit_cycle

/--
[not_noFurtherOdd_oddTrianglePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma not_noFurtherOdd_oddTrianglePair_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  ¬NoFurtherOdd (⟨domain, [headEdge.1, suffixEdge.1]⟩ : BackboneTwoEdgeBondProgram.State (Fin 6)) headEdge.1 suffixEdge.1 (fluxBitConfig domain.graph oddBit oddTrianglePairFlux) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.Cycle.not_noFurtherOdd_oddTrianglePair

/--
[not_program_complete_oddTrianglePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma not_program_complete_oddTrianglePair_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  ¬program.CompleteEvent domain [canonicalEdgeSegment domain.graph headEdge, canonicalEdgeSegment domain.graph suffixEdge] oddTrianglePairFlux := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.Cycle.not_program_complete_oddTrianglePair

/--
[not_selectorSpec_fiber_oddTrianglePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean)
-/
@[path]
private lemma not_selectorSpec_fiber_oddTrianglePair_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  ¬(selectorSpec (V := Fin 6)).toPartialSelector.Fiber domain [canonicalEdgeSegment domain.graph headEdge, canonicalEdgeSegment domain.graph suffixEdge] oddTrianglePairFlux := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.Cycle.not_selectorSpec_fiber_oddTrianglePair


-- created on 2026-10-23
