import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part11
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) = fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R omega) d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega d

/--
[fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d.1) = permOrbitVisitCount (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega)) d.1 d.1 • fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle R omega d

/--
[fkRectMedialBoundaryPrimalOrbitWalk_winding_ne_zero_of_componentTurn_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalOrbitWalk_winding_ne_zero_of_componentTurn_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
-- given
  (hturn : FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) ((fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk d) = 0) :
-- imply
  fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d) ≠ (0, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalOrbitWalk_winding_ne_zero_of_componentTurn_eq_zero R omega d hturn

/--
[fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {w : (fkRectOpenGraph R omega).Walk x x}
  {d : FKMedialDart R.medialTorus} :
-- imply
  ¬ FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d)) (fkRectWalkWinding R w) := by
-- proof
  apply StatMech.FrontierD.fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration R omega w d

/--
[fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {x : R.Vertex}
  {w : (fkRectOpenGraph R omega).Walk x x} :
-- imply
  (fkRectWalkWinding R w).2 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder R omega C w

/--
[not_fkRectHasNet_of_zeroTurnRemainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma not_fkRectHasNet_of_zeroTurnRemainder_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  ¬ FKRectHasNet R omega := by
-- proof
  apply StatMech.FrontierD.not_fkRectHasNet_of_zeroTurnRemainder R omega C

/--
[fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {d : FKMedialDart R.medialTorus} :
-- imply
  (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder R omega C d

/--
[fkRectBlackBoundaryPrimalCycleWalk_verticalWinding_eq_zero_of_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrimalCycleWalk_verticalWinding_eq_zero_of_remainder_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrimalCycleWalk_verticalWinding_eq_zero_of_remainder R omega C d

/--
[fkRectZeroTurnRemainderOrientedDart_checkerColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderOrientedDart_checkerColor_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {color : Bool} :
-- imply
  fkMedialCheckerColor (fkRectZeroTurnRemainderOrientedDart R omega C color) = color := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderOrientedDart_checkerColor R omega C color

/--
[fkRectZeroTurnRemainderOrientedDart_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderOrientedDart_component_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {color : Bool} :
-- imply
  (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (fkRectZeroTurnRemainderOrientedDart R omega C color) = C.1 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderOrientedDart_component R omega C color

/--
[fkRectZeroTurnRemainderOrientedDart_winding_fst_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderOrientedDart_winding_fst_pos_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {color : Bool} :
-- imply
  0 < (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega (fkRectZeroTurnRemainderOrientedDart R omega C color))).1 ↔ fkRectZeroTurnRemainderSide R omega C = !color := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderOrientedDart_winding_fst_pos_iff R omega C color

/--
[fkRectZeroTurnRemainderOrientedDart_winding_fst_neg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainderOrientedDart_winding_fst_neg_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {color : Bool} :
-- imply
  (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega (fkRectZeroTurnRemainderOrientedDart R omega C color))).1 < 0 ↔ fkRectZeroTurnRemainderSide R omega C = color := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainderOrientedDart_winding_fst_neg_iff R omega C color

/--
[fkRectRawPrimalCrossingBase_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingBase_component_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  (fkRectOpenGraph R (fkRectForceCutClosed R omega)).connectedComponentMk (fkRectRawPrimalCrossingBase R omega X) = X.1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingBase_component R omega X

/--
[fkRectRawPrimalCrossingBase_torusComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingBase_torusComponent_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  (fkRectOpenGraph R omega).connectedComponentMk (fkRectRawPrimalCrossingBase R omega X) = fkRectRawPrimalCrossingTorusComponent R omega X := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingBase_torusComponent R omega X

/--
[fkRectRawPrimalCrossingVerticalPotential_eq_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingVerticalPotential_eq_walk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {y : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk (fkRectRawPrimalCrossingBase R omega X) y} :
-- imply
  fkRectRawPrimalCrossingVerticalPotential R omega X y = (fkRectWalkWinding R p).2 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingVerticalPotential_eq_walk R omega C X p

/--
[fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {x y : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk x y}
-- given
  (hx : (fkRectOpenGraph R omega).Reachable (fkRectRawPrimalCrossingBase R omega X) x) :
-- imply
  fkRectRawPrimalCrossingVerticalPotential R omega X y - fkRectRawPrimalCrossingVerticalPotential R omega X x = (fkRectWalkWinding R p).2 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk R omega C X hx p

/--
[mem_fkRectRawPrimalCrossingTorusVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma mem_fkRectRawPrimalCrossingTorusVertices_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {y : R.Vertex} :
-- imply
  y ∈ fkRectRawPrimalCrossingTorusVertices R omega X ↔ (fkRectOpenGraph R omega).connectedComponentMk y = fkRectRawPrimalCrossingTorusComponent R omega X := by
-- proof
  apply StatMech.FrontierD.mem_fkRectRawPrimalCrossingTorusVertices R omega X y

/--
[fkRectRawPrimalCrossingBase_mem_torusVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingBase_mem_torusVertices_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  fkRectRawPrimalCrossingBase R omega X ∈ fkRectRawPrimalCrossingTorusVertices R omega X := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingBase_mem_torusVertices R omega X

/--
[fkRectRawPrimalCrossingTorusVertices_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingTorusVertices_nonempty_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  (fkRectRawPrimalCrossingTorusVertices R omega X).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingTorusVertices_nonempty R omega X

/--
[fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {y : R.Vertex}
-- given
  (hy : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X) :
-- imply
  (fkRectOpenGraph R omega).Reachable (fkRectRawPrimalCrossingBase R omega X) y := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices R omega X hy

/--
[fkRectRawPrimalCrossingDevelopedHeights_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedHeights_nonempty_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  (fkRectRawPrimalCrossingDevelopedHeights R omega X).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedHeights_nonempty R omega X

/--
[fkRectRawPrimalCrossingBottomVertex_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingBottomVertex_spec_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  fkRectRawPrimalCrossingBottomVertex R omega X ∈ fkRectRawPrimalCrossingTorusVertices R omega X ∧ fkRectRawPrimalCrossingDevelopedHeight R omega X (fkRectRawPrimalCrossingBottomVertex R omega X) = fkRectRawPrimalCrossingMinDevelopedHeight R omega X := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingBottomVertex_spec R omega X

/--
[fkRectRawPrimalCrossingTopVertex_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingTopVertex_spec_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  fkRectRawPrimalCrossingTopVertex R omega X ∈ fkRectRawPrimalCrossingTorusVertices R omega X ∧ fkRectRawPrimalCrossingDevelopedHeight R omega X (fkRectRawPrimalCrossingTopVertex R omega X) = fkRectRawPrimalCrossingMaxDevelopedHeight R omega X := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingTopVertex_spec R omega X

/--
[fkRectRawPrimalCrossingDevelopedHeight_sub_eq_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedHeight_sub_eq_walk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {x y : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk x y}
-- given
  (hx : (fkRectOpenGraph R omega).Reachable (fkRectRawPrimalCrossingBase R omega X) x) :
-- imply
  fkRectRawPrimalCrossingDevelopedHeight R omega X y - fkRectRawPrimalCrossingDevelopedHeight R omega X x = (y.2.val : Int) - x.2.val + (R.height : Int) * (fkRectWalkWinding R p).2 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedHeight_sub_eq_walk R omega C X hx p

/--
[fkRectRawPrimalCrossingDevelopedHeight_verticalPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedHeight_verticalPred_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {x : R.Vertex}
-- given
  (hx : (fkRectOpenGraph R omega).Reachable (fkRectRawPrimalCrossingBase R omega X) x)
  (hpred : (fkRectOpenGraph R omega).Adj x (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)) :
-- imply
  fkRectRawPrimalCrossingDevelopedHeight R omega X (x.1, SixVertexArrows.cyclicPred R.height_pos x.2) = fkRectRawPrimalCrossingDevelopedHeight R omega X x - 1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedHeight_verticalPred R omega C X x hx hpred

/--
[fkRectRawPrimalCrossingBottomEdge_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingBottomEdge_closed_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  omega (true, fkRectRawPrimalCrossingBottomVertex R omega X) = false := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingBottomEdge_closed R omega C X

/--
[fkRectRawPrimalCrossingDevelopedHeight_verticalSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedHeight_verticalSucc_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {x : R.Vertex}
-- given
  (hx : (fkRectOpenGraph R omega).Reachable (fkRectRawPrimalCrossingBase R omega X) x)
  (hsucc : (fkRectOpenGraph R omega).Adj x (x.1, finitePeriodicSucc R.height_pos x.2)) :
-- imply
  fkRectRawPrimalCrossingDevelopedHeight R omega X (x.1, finitePeriodicSucc R.height_pos x.2) = fkRectRawPrimalCrossingDevelopedHeight R omega X x + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedHeight_verticalSucc R omega C X x hx hsucc

/--
[fkRectRawPrimalCrossingTopClosing_verticalWinding_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingTopClosing_verticalWinding_neg_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {p : (fkRectOpenGraph R omega).Walk (fkRectRawPrimalCrossingTopVertex R omega X) ((fkRectRawPrimalCrossingTopVertex R omega X).1, finitePeriodicSucc R.height_pos (fkRectRawPrimalCrossingTopVertex R omega X).2)} :
-- imply
  (fkRectWalkWinding R p).2 + fkRectVerticalSeamIncrement R ((fkRectRawPrimalCrossingTopVertex R omega X).1, finitePeriodicSucc R.height_pos (fkRectRawPrimalCrossingTopVertex R omega X).2) (fkRectRawPrimalCrossingTopVertex R omega X) < 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingTopClosing_verticalWinding_neg R omega C X p

/--
[fkRectRawPrimalCrossingBottomClosing_verticalWinding_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingBottomClosing_verticalWinding_pos_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {p : (fkRectOpenGraph R omega).Walk (fkRectRawPrimalCrossingBottomVertex R omega X) ((fkRectRawPrimalCrossingBottomVertex R omega X).1, SixVertexArrows.cyclicPred R.height_pos (fkRectRawPrimalCrossingBottomVertex R omega X).2)} :
-- imply
  0 < (fkRectWalkWinding R p).2 + fkRectVerticalSeamIncrement R ((fkRectRawPrimalCrossingBottomVertex R omega X).1, SixVertexArrows.cyclicPred R.height_pos (fkRectRawPrimalCrossingBottomVertex R omega X).2) (fkRectRawPrimalCrossingBottomVertex R omega X) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingBottomClosing_verticalWinding_pos R omega C X p

/--
[fkRectRawPrimalCrossingTopEdge_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingTopEdge_closed_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega} :
-- imply
  omega (true, ((fkRectRawPrimalCrossingTopVertex R omega X).1, finitePeriodicSucc R.height_pos (fkRectRawPrimalCrossingTopVertex R omega X).2)) = false := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingTopEdge_closed R omega C X

/--
[fkRectMedialDartAbovePrimalVertex_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectMedialDartAbovePrimalVertex_label_eq
  {R : FKRectTorus}
  {x : R.Vertex} :
-- imply
  fkRectMedialDartPrimalLabel R (fkRectMedialDartAbovePrimalVertex R x) = x := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDartAbovePrimalVertex_label R x

/--
[fkRectRawPrimalCrossingDevelopedExtremeDart_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeDart_label_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool} :
-- imply
  fkRectMedialDartPrimalLabel R (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side) = if side then fkRectRawPrimalCrossingTopVertex R omega X else fkRectRawPrimalCrossingBottomVertex R omega X := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeDart_label R omega X side

/--
[fkRectRawPrimalCrossingDevelopedExtremeDart_primalComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeDart_primalComponent_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool} :
-- imply
  fkRectMedialComponentToPrimalComponent R omega ((fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side)) = fkRectRawPrimalCrossingTorusComponent R omega X := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeDart_primalComponent R omega X side

/--
[fkRectRawPrimalCrossingDevelopedExtremeDart_matches_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeDart_matches_component_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
-- given
  (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C) :
-- imply
  fkRectMedialComponentToPrimalComponent R omega ((fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X (fkRectZeroTurnRemainderSide R omega C))) = fkRectZeroTurnRemainderPrimalComponent R omega C := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeDart_matches_component R omega C X hX

/--
[fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean)
-/
@[path]
private lemma fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C D : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
-- given
  (hincidence : FKRectZeroTurnPrimalDevelopedExtremeIncidence R omega)
  (hXC : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
  (hXD : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega D)
  (hside : fkRectZeroTurnRemainderSide R omega C = fkRectZeroTurnRemainderSide R omega D) :
-- imply
  C = D := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing R omega hincidence C D X hXC hXD hside


-- created on 2026-10-23
