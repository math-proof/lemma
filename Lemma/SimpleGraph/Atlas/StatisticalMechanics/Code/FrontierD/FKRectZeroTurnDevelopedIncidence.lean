import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectRawPrimalCrossingDevelopedExtremeEdge_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeEdge_false_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X false = (true, fkRectRawPrimalCrossingBottomVertex R omega X) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeEdge_false R omega X

/--
[fkRectRawPrimalCrossingDevelopedExtremeEdge_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeEdge_true_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X true = (true, ((fkRectRawPrimalCrossingTopVertex R omega X).1, finitePeriodicSucc R.height_pos (fkRectRawPrimalCrossingTopVertex R omega X).2)) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeEdge_true R omega X

/--
[fkRectRawPrimalCrossingDevelopedExtremeDart_eq_west_or_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeDart_eq_west_or_east_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool} :
-- imply
  fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side = fkMedialWestDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side)) ∨ fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side = fkMedialEastDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side)) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeDart_eq_west_or_east R omega X side

/--
[fkRectRawPrimalCrossingDevelopedExtremeWest_checkerColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeWest_checkerColor_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool}
-- given
  (hd : fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side = fkMedialWestDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side))) :
-- imply
  fkMedialCheckerColor (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side) = !side := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeWest_checkerColor R omega X side hd

/--
[fkRectRawPrimalCrossingDevelopedExtremeEast_checkerColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeEast_checkerColor_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool}
-- given
  (hd : fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side = fkMedialEastDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side))) :
-- imply
  fkMedialCheckerColor (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side) = side := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeEast_checkerColor R omega X side hd

/--
[fkRectRawPrimalCrossingDevelopedExtremeFundamental_vertical_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeFundamental_vertical_ne_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {C : FKRectZeroTurnCutRemainderComponent R (fkRectConfigurationOfEdges R F)}
  {X : FKRectRawPrimalHorizontalCrossingComponent R (fkRectConfigurationOfEdges R F)}
  {side : Bool}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side)) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side))} :
-- imply
  (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side) r)).2 ≠ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeFundamental_vertical_ne_zero R F C X side r

/--
[fkRectRawPrimalCrossingDevelopedExtremeWest_winding_fst_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeWest_winding_fst_pos_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {C : FKRectZeroTurnCutRemainderComponent R (fkRectConfigurationOfEdges R F)}
  {X : FKRectRawPrimalHorizontalCrossingComponent R (fkRectConfigurationOfEdges R F)}
  {side : Bool}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side)) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side))}
-- given
  (heF : fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side))) (fkMedialEastDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side))))
  (hd : fkRectRawPrimalCrossingDevelopedExtremeDart R (fkRectConfigurationOfEdges R F) X side = fkMedialWestDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side))) :
-- imply
  0 < (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) (fkRectRawPrimalCrossingDevelopedExtremeDart R (fkRectConfigurationOfEdges R F) X side))).1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeWest_winding_fst_pos R F C X side r heF hsep hd

/--
[fkRectRawPrimalCrossingDevelopedExtremeEast_winding_fst_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeEast_winding_fst_neg_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {C : FKRectZeroTurnCutRemainderComponent R (fkRectConfigurationOfEdges R F)}
  {X : FKRectRawPrimalHorizontalCrossingComponent R (fkRectConfigurationOfEdges R F)}
  {side : Bool}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side)) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side))}
-- given
  (heF : fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side))) (fkMedialEastDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side))))
  (hd : fkRectRawPrimalCrossingDevelopedExtremeDart R (fkRectConfigurationOfEdges R F) X side = fkMedialEastDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X side))) :
-- imply
  (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) (fkRectRawPrimalCrossingDevelopedExtremeDart R (fkRectConfigurationOfEdges R F) X side))).1 < 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeEast_winding_fst_neg R F C X side r heF hsep hd

/--
[fkRectRawPrimalCrossingDevelopedExtremeWest_reachable_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeWest_reachable_remainder_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool}
-- given
  (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
  (hwe : (fkRectOpenGraph R omega).Reachable (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side)) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side))) :
-- imply
  (fkRectOpenGraph R omega).Reachable (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X side)) (fkRectMedialDartPrimalLabel R (fkRectZeroTurnRemainderBlackDart R omega C).1) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeWest_reachable_remainder R omega C X side hX hwe

/--
[fkRectRawPrimalCrossingDevelopedExtreme_not_reachable_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtreme_not_reachable_edges_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {C : FKRectZeroTurnCutRemainderComponent R (fkRectConfigurationOfEdges R F)}
  {X : FKRectRawPrimalHorizontalCrossingComponent R (fkRectConfigurationOfEdges R F)}
-- given
  (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R (fkRectConfigurationOfEdges R F) C) :
-- imply
  ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X (fkRectZeroTurnRemainderSide R (fkRectConfigurationOfEdges R F) C)))) (fkMedialEastDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X (fkRectZeroTurnRemainderSide R (fkRectConfigurationOfEdges R F) C)))) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtreme_not_reachable_edges R F C X hX

/--
[fkRectRawPrimalCrossingDevelopedExtreme_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtreme_not_reachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
-- given
  (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C) :
-- imply
  ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C)))) (fkMedialEastDart (fkRectMedialVertexOfEdge R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C)))) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtreme_not_reachable R omega C X hX

/--
[fkRectZeroTurnRemainderOrientedDart_avoids_developedExtreme_localSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderOrientedDart_avoids_developedExtreme_localSides_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
-- given
  (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
  (hendpoint : ¬ (fkRectOpenGraph R omega).Reachable (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C))) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C))))
  (hcomponent : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X (fkRectZeroTurnRemainderSide R omega C)) ≠ C.1) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R omega let e := fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C) let dA := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X (fkRectZeroTurnRemainderSide R omega C) let dB := fkRectZeroTurnRemainderOrientedDart R omega C (fkMedialCheckerColor dA) ∀ k : Nat, (fkMedialBoundaryStep pairing)^[k] dB ≠ fkMedialWestDart (fkRectMedialVertexOfEdge R e) ∧ (fkMedialBoundaryStep pairing)^[k] dB ≠ fkMedialEastDart (fkRectMedialVertexOfEdge R e) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderOrientedDart_avoids_developedExtreme_localSides R omega C X hX hendpoint hcomponent

/--
[fkRectZeroTurnRemainderOrientedDart_developedExtreme_interaction_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderOrientedDart_developedExtreme_interaction_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {C : FKRectZeroTurnCutRemainderComponent R (fkRectConfigurationOfEdges R F)}
  {X : FKRectRawPrimalHorizontalCrossingComponent R (fkRectConfigurationOfEdges R F)}
-- given
  (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R (fkRectConfigurationOfEdges R F) C)
  (hendpoint : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X (fkRectZeroTurnRemainderSide R (fkRectConfigurationOfEdges R F) C))) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X (fkRectZeroTurnRemainderSide R (fkRectConfigurationOfEdges R F) C))))
  (hcomponent : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).connectedComponentMk (fkRectRawPrimalCrossingDevelopedExtremeDart R (fkRectConfigurationOfEdges R F) X (fkRectZeroTurnRemainderSide R (fkRectConfigurationOfEdges R F) C)) ≠ C.1) :
-- imply
  let omega := fkRectConfigurationOfEdges R F let e := fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C) let dA := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X (fkRectZeroTurnRemainderSide R omega C) let dB := fkRectZeroTurnRemainderOrientedDart R omega C (fkMedialCheckerColor dA) let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) fkRectRefinedRawInteraction B ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderOrientedDart_developedExtreme_interaction_eq_zero R F C X hX hendpoint hcomponent

/--
[fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointWalk_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {C : FKRectZeroTurnCutRemainderComponent R (fkRectConfigurationOfEdges R F)}
  {X : FKRectRawPrimalHorizontalCrossingComponent R (fkRectConfigurationOfEdges R F)}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X (fkRectZeroTurnRemainderSide R (fkRectConfigurationOfEdges R F) C))) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R (fkRectConfigurationOfEdges R F) X (fkRectZeroTurnRemainderSide R (fkRectConfigurationOfEdges R F) C)))}
-- given
  (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R (fkRectConfigurationOfEdges R F) C) :
-- imply
  (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).connectedComponentMk (fkRectRawPrimalCrossingDevelopedExtremeDart R (fkRectConfigurationOfEdges R F) X (fkRectZeroTurnRemainderSide R (fkRectConfigurationOfEdges R F) C)) = C.1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointWalk R F C X hX r

/--
[fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointReachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
-- given
  (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
  (hreach : (fkRectOpenGraph R omega).Reachable (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C))) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C)))) :
-- imply
  (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X (fkRectZeroTurnRemainderSide R omega C)) = C.1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointReachable R omega C X hX hreach

/--
[fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing_of_endpointReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing_of_endpointReachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
-- given
  (hXC : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
  (hXD : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega D)
  (hreachC : (fkRectOpenGraph R omega).Reachable (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C))) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C))))
  (hreachD : (fkRectOpenGraph R omega).Reachable (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega D))) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega D))))
  (hside : fkRectZeroTurnRemainderSide R omega C = fkRectZeroTurnRemainderSide R omega D) :
-- imply
  C = D := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing_of_endpointReachable R omega C D X hXC hXD hreachC hreachD hside

/--
[fkRectPrimalBoundaryFiberSameSignUnique_of_card_nonzero_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectPrimalBoundaryFiberSameSignUnique_of_card_nonzero_le_two_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hcard : ¬ FKRectHasNet R omega → ∀ x : R.Vertex, (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2) :
-- imply
  FKRectPrimalBoundaryFiberSameSignUnique R omega := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalBoundaryFiberSameSignUnique_of_card_nonzero_le_two R omega hcard

/--
[fkRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence_of_regularNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence_of_regularNeighborhood_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hregular : FKRectPrimalRankOneRegularNeighborhood R omega) :
-- imply
  FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence_of_regularNeighborhood R omega hregular

/--
[fkRectZeroTurnPrimalDevelopedExtremeIncidence_of_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean)
-/
@[path]
private lemma fkRectZeroTurnPrimalDevelopedExtremeIncidence_of_disconnected_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hdisconnected : FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega) :
-- imply
  FKRectZeroTurnPrimalDevelopedExtremeIncidence R omega := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnPrimalDevelopedExtremeIncidence_of_disconnected R omega hdisconnected


-- created on 2026-10-23
