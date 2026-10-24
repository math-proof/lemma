import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelector
open SimpleGraph Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.BackboneConcreteSelector


/--
[bondwiseSuffixEvent_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean)
-/
@[path]
private lemma bondwiseSuffixEvent_nil_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {x : D}
-- given
  (bit : Nat -> Bool)
  (m : G.edgeFinset -> Nat) :
-- imply
  BondwiseSuffixEvent G X x [] bit m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.bondwiseSuffixEvent_nil G X x bit m

/--
[no_nilFiber_iff_bondwiseSuffixEvent_of_sources_ne_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean)
-/
@[path]
private lemma no_nilFiber_iff_bondwiseSuffixEvent_of_sources_ne_empty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {x : D}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (m : d.graph.edgeFinset -> Nat)
  (bit : Nat -> Bool)
  (hsrc : sources d.graph (ofEdgeFun d.graph m) ≠ ∅) :
-- imply
  ¬(S.Fiber d [] m ↔ BondwiseSuffixEvent d.graph X x [] bit m) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.no_nilFiber_iff_bondwiseSuffixEvent_of_sources_ne_empty S d m X x bit hsrc

/--
[no_functional_fiber_bridge_of_nonempty_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean)
-/
@[path]
private lemma no_functional_fiber_bridge_of_nonempty_event_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {x : D}
  {bonds : List (Sym2 V)}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (m : d.graph.edgeFinset -> Nat)
  (bit : Nat -> Bool)
  (decode : List (Sym2 V) -> List (shb_ExplorationSegment V))
  (hdecode : decode [] ≠ decode bonds)
  (hbonds : BondwiseSuffixEvent d.graph X x bonds bit m)
  (hbridge : forall bs, S.Fiber d (decode bs) m <-> BondwiseSuffixEvent d.graph X x bs bit m) :
-- imply
  False := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.no_functional_fiber_bridge_of_nonempty_event S d m X x bit bonds decode hdecode hbonds hbridge

/--
[completeEvent_fluxEventOutsideCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean)
-/
@[path]
private lemma completeEvent_fluxEventOutsideCut_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
  {x : P.State}
  {accepted : Sym2 V}
-- given
  (hstate : P.initial d = P.scan.advance x accepted)
  (hfresh : SuffixFresh P.scan x accepted (P.encode d word))
  (m : d.graph.edgeFinset -> Nat)
  (hterminal : FluxEventOutsideCut d.graph m ((P.scan.bondwiseOrdered.tests x).determinedCut accepted) (P.TerminalEvent d word)) :
-- imply
  FluxEventOutsideCut d.graph m ((P.scan.bondwiseOrdered.tests x).determinedCut accepted) (P.CompleteEvent d word) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.completeEvent_fluxEventOutsideCut P d word x accepted hstate hfresh m hterminal

/--
[CompleteBondwiseSelectorSpec.fiber_iff_completeEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean)
-/
@[path]
private lemma fiber_iff_completeEvent_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  R.toPartialSelector.Fiber d word m <-> P.CompleteEvent d word m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.fiber_iff_completeEvent R d word m

/--
[CompleteBondwiseSelectorSpec.fiber_iff_bondwiseSuffixEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean)
-/
@[path]
private lemma fiber_iff_bondwiseSuffixEvent_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (hterminal : P.TerminalEvent d word m) :
-- imply
  R.toPartialSelector.Fiber d word m ↔ BondwiseSuffixEvent d.graph P.scan (P.initial d) (P.encode d word) P.bit m := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.fiber_iff_bondwiseSuffixEvent R d word m hterminal

/--
[CompleteBondwiseSelectorSpec.fiber_fluxEventOutsideCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean)
-/
@[path]
private lemma fiber_fluxEventOutsideCut_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {P : BondwiseSegmentProgram V}
  {R : CompleteBondwiseSelectorSpec P}
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
  {x : P.State}
  {accepted : Sym2 V}
-- given
  (hstate : P.initial d = P.scan.advance x accepted)
  (hfresh : SuffixFresh P.scan x accepted (P.encode d word))
  (m : d.graph.edgeFinset -> Nat)
  (hterminal : FluxEventOutsideCut d.graph m ((P.scan.bondwiseOrdered.tests x).determinedCut accepted) (P.TerminalEvent d word)) :
-- imply
  FluxEventOutsideCut d.graph m ((P.scan.bondwiseOrdered.tests x).determinedCut accepted) (R.toPartialSelector.Fiber d word) := by
-- proof
  apply StatMech.Sharpness.BackboneConcreteSelector.CompleteBondwiseSelectorSpec.fiber_fluxEventOutsideCut R d word x accepted hstate hfresh m hterminal


-- created on 2026-10-23
