import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact
open Equiv StatMech StatMech.FrontierD


/--
[fkMedialTogglePairingAt_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma fkMedialTogglePairingAt_comm_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex} :
-- imply
  fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing first) second = fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing second) first := by
-- proof
  apply StatMech.FrontierD.fkMedialTogglePairingAt_comm pairing first second

/--
[sixVertexRetieAtTransitionVertices_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma sixVertexRetieAtTransitionVertices_self_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex} :
-- imply
  sixVertexRetieAtTransitionVertices (sixVertexRetieAtTransitionVertices pairing first second) first second = pairing := by
-- proof
  apply StatMech.FrontierD.sixVertexRetieAtTransitionVertices_self pairing first second

/--
[sixVertexRetieAtTransitionVertices_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma sixVertexRetieAtTransitionVertices_of_eq_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex}
-- given
  (hvertices : first = second) :
-- imply
  sixVertexRetieAtTransitionVertices pairing first second = fkMedialTogglePairingAt pairing first := by
-- proof
  apply StatMech.FrontierD.sixVertexRetieAtTransitionVertices_of_eq pairing hvertices

/--
[sixVertexRetieAtTransitionVertices_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma sixVertexRetieAtTransitionVertices_of_ne_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex}
-- given
  (hvertices : first ≠ second) :
-- imply
  sixVertexRetieAtTransitionVertices pairing first second = fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing first) second := by
-- proof
  apply StatMech.FrontierD.sixVertexRetieAtTransitionVertices_of_ne pairing hvertices

/--
[fkMedialBlackBoundaryPerm_retie_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_retie_of_eq_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex}
-- given
  (hvertices : first = second) :
-- imply
  fkMedialBlackBoundaryPerm (sixVertexRetieAtTransitionVertices pairing first second) = fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartSwap first := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_retie_of_eq pairing hvertices

/--
[fkMedialBlackBoundaryPerm_retie_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_retie_of_ne_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex}
-- given
  (hvertices : first ≠ second) :
-- imply
  fkMedialBlackBoundaryPerm (sixVertexRetieAtTransitionVertices pairing first second) = (fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartSwap first) * fkMedialBlackDartSwap second := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_retie_of_ne pairing hvertices

/--
[fkColoredStrandSlotBoundaryPerm_retie_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma fkColoredStrandSlotBoundaryPerm_retie_of_eq_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex}
-- given
  (hvertices : first = second) :
-- imply
  fkColoredStrandSlotBoundaryPerm (sixVertexRetieAtTransitionVertices pairing first second) = if fkMedialVertexParity first = true then (fkColoredStrandSlotBoundaryPerm pairing).trans (fkColoredVertexStrandSlotSwap first) else (fkColoredVertexStrandSlotSwap first).trans (fkColoredStrandSlotBoundaryPerm pairing) := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSlotBoundaryPerm_retie_of_eq pairing hvertices

/--
[fkColoredStrandSlotBoundaryPerm_retie_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma fkColoredStrandSlotBoundaryPerm_retie_of_ne_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex}
-- given
  (hvertices : first != second) :
-- imply
  fkColoredStrandSlotBoundaryPerm (sixVertexRetieAtTransitionVertices pairing first second) = if fkMedialVertexParity second = true then (if fkMedialVertexParity first = true then (fkColoredStrandSlotBoundaryPerm pairing).trans (fkColoredVertexStrandSlotSwap first) else (fkColoredVertexStrandSlotSwap first).trans (fkColoredStrandSlotBoundaryPerm pairing)).trans (fkColoredVertexStrandSlotSwap second) else (fkColoredVertexStrandSlotSwap second).trans (if fkMedialVertexParity first = true then (fkColoredStrandSlotBoundaryPerm pairing).trans (fkColoredVertexStrandSlotSwap first) else (fkColoredVertexStrandSlotSwap first).trans (fkColoredStrandSlotBoundaryPerm pairing)) := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSlotBoundaryPerm_retie_of_ne pairing hvertices

/--
[doubledAlignedFirstReturnPerm_sameCycle_falseBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma doubledAlignedFirstReturnPerm_sameCycle_falseBoundary_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x y : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hcycle : (doubledAlignedFirstReturnPerm homega heta hdegree).SameCycle x y) :
-- imply
  (alignedBoundaryPerm homega heta hdegree false).SameCycle (doubledAlignedBlackDart homega heta hdegree false x) (doubledAlignedBlackDart homega heta hdegree false y) := by
-- proof
  apply StatMech.FrontierD.doubledAlignedFirstReturnPerm_sameCycle_falseBoundary homega heta hdegree hcycle

/--
[fkMedialLayeredTwoCutBalanced_of_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma fkMedialLayeredTwoCutBalanced_of_balance_eq
  {T : EvenTorus}
  {first second : T.Vertex}
-- given
  (source : Bool -> FKMedialLoopPairing T)
  (hbalance : FKMedialLayeredTwoCutBalance source first second) :
-- imply
  FKMedialLayeredTwoCutBalanced source first second := by
-- proof
  apply StatMech.FrontierD.fkMedialLayeredTwoCutBalanced_of_balance source first second hbalance

/--
[intCast_fkMedialLoopCount_twoToggle_sub_eq_splitScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma intCast_fkMedialLoopCount_twoToggle_sub_eq_splitScore_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex} :
-- imply
  (fkMedialLoopCount T (fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing first) second) : Int) - fkMedialLoopCount T pairing = FKMedialTwoCutSplitScore pairing first second := by
-- proof
  apply StatMech.FrontierD.intCast_fkMedialLoopCount_twoToggle_sub_eq_splitScore pairing first second

/--
[fkMedialLayeredTwoCutBalanced_iff_loopCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma fkMedialLayeredTwoCutBalanced_iff_loopCount_eq_eq
  {T : EvenTorus}
  {first second : T.Vertex}
-- given
  (source : Bool -> FKMedialLoopPairing T) :
-- imply
  FKMedialLayeredTwoCutBalanced source first second <-> fkMedialLoopCount T (fkMedialTogglePairingAt (fkMedialTogglePairingAt (source false) first) second) + fkMedialLoopCount T (fkMedialTogglePairingAt (fkMedialTogglePairingAt (source true) first) second) = fkMedialLoopCount T (source false) + fkMedialLoopCount T (source true) := by
-- proof
  apply StatMech.FrontierD.fkMedialLayeredTwoCutBalanced_iff_loopCount_eq source first second

/--
[fkMedialLoopCount_retie_add_retie_eq_of_transitionTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma fkMedialLoopCount_retie_add_retie_eq_of_transitionTopology_eq
  {T : EvenTorus}
  {first second : T.Vertex}
-- given
  (source : Bool -> FKMedialLoopPairing T)
  (htopology : FKMedialLayeredTransitionTopology source first second) :
-- imply
  fkMedialLoopCount T (sixVertexRetieAtTransitionVertices (source false) first second) + fkMedialLoopCount T (sixVertexRetieAtTransitionVertices (source true) first second) = fkMedialLoopCount T (source false) + fkMedialLoopCount T (source true) := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCount_retie_add_retie_eq_of_transitionTopology source first second htopology

/--
[sixVertexDegreeTwoAlignedTargetPairing_of_proper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTargetPairing_of_proper_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer = sixVertexRetieAtTransitionVertices (alignedRoutingLoopPairing homega heta hdegree layer) (doubledAlignedVertex (cut.cutRight.head hright)) (doubledAlignedVertex (cut.cutLeft.head hleft)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTargetPairing_of_proper homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer

/--
[sixVertexDegreeTwoAlignedTargetPairing_recover_of_proper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTargetPairing_recover_of_proper_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle sixVertexRetieAtTransitionVertices (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) (doubledAlignedVertex (cut.cutRight.head hright)) (doubledAlignedVertex (cut.cutLeft.head hleft)) = alignedRoutingLoopPairing homega heta hdegree layer := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTargetPairing_recover_of_proper homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer

/--
[sixVertexDegreeTwoAlignedTargetPairing_loopCount_eq_of_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTargetPairing_loopCount_eq_of_alternating_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertices : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) ≠ doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft))
  (halternating : FKMedialAlternatingTwoCut (alignedRoutingLoopPairing homega heta hdegree layer) (doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright)) (doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft))) :
-- imply
  fkMedialLoopCount T (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) = fkMedialLoopCount T (alignedRoutingLoopPairing homega heta hdegree layer) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTargetPairing_loopCount_eq_of_alternating homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer hvertices halternating

/--
[sixVertexDegreeTwoAlignedTargetPairing_totalLoopCount_eq_of_topology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTargetPairing_totalLoopCount_eq_of_topology_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (htopology : FKMedialLayeredTransitionTopology (alignedRoutingLoopPairing homega heta hdegree) (doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright)) (doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft))) :
-- imply
  fkMedialLoopCount T (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle false) + fkMedialLoopCount T (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle true) = fkMedialLoopCount T (alignedRoutingLoopPairing homega heta hdegree false) + fkMedialLoopCount T (alignedRoutingLoopPairing homega heta hdegree true) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTargetPairing_totalLoopCount_eq_of_topology homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright htopology

/--
[doubledAlignedBoundarySegments_step_mem_iff_of_ne_cut_heads](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma doubledAlignedBoundarySegments_step_mem_iff_of_ne_cut_heads_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {dart : FKMedialBlackDart T}
  {y : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hstep : alignedBoundaryPerm homega heta hdegree false dart = doubledAlignedBlackDart homega heta hdegree false y)
  (hneRight : y ≠ (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright)
  (hneLeft : y ≠ (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft) :
-- imply
  alignedBoundaryPerm homega heta hdegree false dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) <-> dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.doubledAlignedBoundarySegments_step_mem_iff_of_ne_cut_heads homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright dart y hstep hneRight hneLeft

/--
[doubledAlignedBoundarySegments_rightHead_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma doubledAlignedBoundarySegments_rightHead_transition_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hstep : alignedBoundaryPerm homega heta hdegree false dart = doubledAlignedBlackDart homega heta hdegree false ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright)) :
-- imply
  alignedBoundaryPerm homega heta hdegree false dart ∉ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) /\ dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.doubledAlignedBoundarySegments_rightHead_transition homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright dart hstep

/--
[doubledAlignedBoundarySegments_leftHead_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma doubledAlignedBoundarySegments_leftHead_transition_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hstep : alignedBoundaryPerm homega heta hdegree false dart = doubledAlignedBlackDart homega heta hdegree false ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  alignedBoundaryPerm homega heta hdegree false dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) /\ dart ∉ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.doubledAlignedBoundarySegments_leftHead_transition homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright dart hstep

/--
[canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertex : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) = doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft = doubledAlignedBranchSwap ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) := by
-- proof
  apply StatMech.FrontierD.canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex

/--
[canonicalDoubledAlignedCut_coincident_oppositeSplits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean)
-/
@[path]
private lemma canonicalDoubledAlignedCut_coincident_oppositeSplits_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertex : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) = doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  FKMedialCutSplits (alignedRoutingLoopPairing homega heta hdegree false) (doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright)) <-> Not (FKMedialCutSplits (alignedRoutingLoopPairing homega heta hdegree true) (doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright))) := by
-- proof
  apply StatMech.FrontierD.canonicalDoubledAlignedCut_coincident_oppositeSplits homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex


-- created on 2026-10-23
