import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
open Finset StatMech StatMech.FrontierD


/--
[fkRectRefined_horizontal_west_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefined_horizontal_west_interaction_eq
  {L : Nat}
  [Fact (8 < L)]
  {x y : ZMod L} :
-- imply
  fkRectRefinedRawInteraction [((x - 1, y - 1), 1), ((x - 1, y), 1)] [((x + 2, y), 2), ((x + 1, y), 2), ((x, y), 2), ((x - 1, y), 2)] = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_horizontal_west_interaction x y

/--
[fkRectRefined_horizontal_east_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefined_horizontal_east_interaction_eq
  {L : Nat}
  [Fact (8 < L)]
  {x y : ZMod L} :
-- imply
  fkRectRefinedRawInteraction [((x + 1, y + 1), 3), ((x + 1, y), 3)] [((x + 2, y), 2), ((x + 1, y), 2), ((x, y), 2), ((x - 1, y), 2)] = -1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_horizontal_east_interaction x y

/--
[fkRectRefined_vertical_west_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefined_vertical_west_interaction_eq
  {L : Nat}
  [Fact (8 < L)]
  {x y : ZMod L} :
-- imply
  fkRectRefinedRawInteraction [((x - 1, y - 1), 0), ((x, y - 1), 0)] [((x, y - 2), 1), ((x, y - 1), 1), ((x, y), 1), ((x, y + 1), 1)] = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_vertical_west_interaction x y

/--
[fkRectRefined_vertical_east_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefined_vertical_east_interaction_eq
  {L : Nat}
  [Fact (8 < L)]
  {x y : ZMod L} :
-- imply
  fkRectRefinedRawInteraction [((x + 1, y + 1), 2), ((x, y + 1), 2)] [((x, y - 2), 1), ((x, y - 1), 1), ((x, y), 1), ((x, y + 1), 1)] = -1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_vertical_east_interaction x y

/--
[fkRectRefinedPrimalEdgeDarts_eq_centerline](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedPrimalEdgeDarts_eq_centerline_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectRefinedPrimalEdgeDarts R e = fkRectRefinedPrimalCenterlineDarts (fkRectClosedPairingAtEdge e) (fkRectRefinedPrimalEdgeCenter R e) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedPrimalEdgeDarts_eq_centerline R e

/--
[fkRectRefinedLocalDarts_west_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedLocalDarts_west_interaction_eq
  {L : Nat}
  [Fact (8 < L)]
  {pairing : Bool}
  {c : Int × Int} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedLocalDarts pairing c .west).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalCenterlineDarts pairing c).map (fkRectIntegralSquareDartMod L)) = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedLocalDarts_west_interaction pairing c

/--
[fkRectRefinedLocalDarts_east_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedLocalDarts_east_interaction_eq
  {L : Nat}
  [Fact (8 < L)]
  {pairing : Bool}
  {c : Int × Int} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedLocalDarts pairing c .east).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalCenterlineDarts pairing c).map (fkRectIntegralSquareDartMod L)) = -1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedLocalDarts_east_interaction pairing c

/--
[fkRectRefinedPrimalEdge_west_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedPrimalEdge_west_interaction_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedLocalDarts (fkRectClosedPairingAtEdge e) (fkRectRefinedPrimalEdgeCenter R e) .west).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod L)) = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedPrimalEdge_west_interaction R e

/--
[fkRectRefinedPrimalEdge_east_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedPrimalEdge_east_interaction_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedLocalDarts (fkRectClosedPairingAtEdge e) (fkRectRefinedPrimalEdgeCenter R e) .east).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod L)) = -1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedPrimalEdge_east_interaction R e

/--
[fkRectRefinedLocalDarts_open_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedLocalDarts_open_interaction_eq
  {L : Nat}
  [Fact (8 < L)]
  {closedPairing : Bool}
  {c : Int × Int}
  {side : FKMedialSide} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedLocalDarts (!closedPairing) c side).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalCenterlineDarts closedPairing c).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedLocalDarts_open_interaction closedPairing c side

/--
[fkRectRefinedScaleDart_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedScaleDart_path_eq
  {L : Nat}
  [Fact (8 < L)]
  {d : FKRectIntegralSquareDart} :
-- imply
  FKRectIntegralSquareDartPath (fkRectRefinedScalePoint d.1) (fkRectRefinedScalePoint (fkRectIntegralSquareDartEnd d)) (fkRectRefinedScaleDart d) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedScaleDart_path d

/--
[FKRectIntegralSquareDartPath.refinedScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma refinedScale_eq
  {L : Nat}
  [Fact (8 < L)]
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p q l) :
-- imply
  FKRectIntegralSquareDartPath (fkRectRefinedScalePoint p) (fkRectRefinedScalePoint q) (fkRectRefinedScaleDarts l) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.refinedScale h

/--
[FKRectSquareWalkLift.exists_refinedDartPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma exists_refinedDartPath_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  ∃ l : List FKRectIntegralSquareDart, FKRectIntegralSquareDartPath (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)) (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) l := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.exists_refinedDartPath R h

/--
[FKRectSquareWalkLift.exists_refinedSquareCoverCycleWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma exists_refinedSquareCoverCycleWitness_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  Nonempty (FKRectSquareCoverCycleWitness R (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1, 4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.exists_refinedSquareCoverCycleWitness R h

/--
[FKRectSquareWalkLift.exists_refinedLargeCoverCycleWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma exists_refinedLargeCoverCycleWitness_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  Nonempty (FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R) (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1, 4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.exists_refinedLargeCoverCycleWitness R h

/--
[FKRectSquareWalkLift.windingIndependent_of_refinedIntersection_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma windingIndependent_of_refinedIntersection_ne_zero_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {G H : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x x}
  {z : H.Walk y y}
  {p q a b : Int × Int}
  {C : FKRectSquareCoverCycleWitness R (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1, 4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)}
  {D : FKRectSquareCoverCycleWitness R (4 * (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a).1, 4 * (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a).2)}
-- given
  (hw : FKRectSquareWalkLift R w p q)
  (hz : FKRectSquareWalkLift R z a b)
  (hne : C.cycle.intersection D.cycle ≠ 0) :
-- imply
  FKRectWindingIndependent (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.windingIndependent_of_refinedIntersection_ne_zero R hw hz C D hne

/--
[fkRectRefinedBoundaryBondCenter_eq_canonical_add_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryBondCenter_eq_canonical_add_deck_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectRefinedBondCenter (fkRectRefinedBoundaryCanonicalCenter R d) (fkMedialLocalMate pairing d).2 = ((fkRectRefinedBoundaryCanonicalCenter R (fkMedialBoundaryStep pairing d)).1 + 4 * (fkRectSquareDeckTranslation R (fkRectMedialBoundaryPrimalSeamIncrement R pairing d)).1 + (fkRectRefinedBoundaryPrimalPotential R d).1 - (fkRectRefinedBoundaryPrimalPotential R (fkMedialBoundaryStep pairing d)).1, (fkRectRefinedBoundaryCanonicalCenter R (fkMedialBoundaryStep pairing d)).2 + 4 * (fkRectSquareDeckTranslation R (fkRectMedialBoundaryPrimalSeamIncrement R pairing d)).2 + (fkRectRefinedBoundaryPrimalPotential R d).2 - (fkRectRefinedBoundaryPrimalPotential R (fkMedialBoundaryStep pairing d)).2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryBondCenter_eq_canonical_add_deck R pairing d

/--
[fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {t : Int × Int}
  {n : Nat} :
-- imply
  fkRectRefinedBoundaryCenterAfter pairing d ((fkRectRefinedBoundaryCanonicalCenter R d).1 + t.1, (fkRectRefinedBoundaryCanonicalCenter R d).2 + t.2) n = ((fkRectRefinedBoundaryCanonicalCenter R ((fkMedialBoundaryStep pairing)^[n] d)).1 + t.1 + 4 * (fkRectSquareDeckTranslation R (fkRectMedialBoundaryPrimalSeamTrace R pairing d n)).1 + (fkRectRefinedBoundaryPrimalPotential R d).1 - (fkRectRefinedBoundaryPrimalPotential R ((fkMedialBoundaryStep pairing)^[n] d)).1, (fkRectRefinedBoundaryCanonicalCenter R ((fkMedialBoundaryStep pairing)^[n] d)).2 + t.2 + 4 * (fkRectSquareDeckTranslation R (fkRectMedialBoundaryPrimalSeamTrace R pairing d n)).2 + (fkRectRefinedBoundaryPrimalPotential R d).2 - (fkRectRefinedBoundaryPrimalPotential R ((fkMedialBoundaryStep pairing)^[n] d)).2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck R pairing d t n

/--
[fkRectMedialBoundaryPrimalStepWalk_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalStepWalk_winding_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectWalkWinding R (fkRectMedialBoundaryPrimalStepWalk R omega d) = fkRectMedialBoundaryPrimalSeamIncrement R (fkRectConfigurationToMedialPairing R omega) d := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalStepWalk_winding R omega d

/--
[fkRectMedialBoundaryPrimalTrace_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalTrace_winding_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
  {n : Nat} :
-- imply
  fkRectWalkWinding R (fkRectMedialBoundaryPrimalTrace R omega d n) = fkRectMedialBoundaryPrimalSeamTrace R (fkRectConfigurationToMedialPairing R omega) d n := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalTrace_winding R omega d n

/--
[fkRectRefinedBoundaryOrbit_exists_squareCoverCycleWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryOrbit_exists_squareCoverCycleWitness_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int} :
-- imply
  Nonempty (FKRectSquareCoverCycleWitness R (fkRectRefinedBoundaryOrbitTranslation pairing d c)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryOrbit_exists_squareCoverCycleWitness R pairing d c

/--
[fkRectRefinedBoundaryOrbit_exists_largeCoverCycleWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryOrbit_exists_largeCoverCycleWitness_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int} :
-- imply
  Nonempty (FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R) (fkRectRefinedBoundaryOrbitTranslation pairing d c)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryOrbit_exists_largeCoverCycleWitness R pairing d c

/--
[fkRectMedialBoundaryPrimalOrbitWalk_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalOrbitWalk_winding_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d) = fkRectMedialBoundaryPrimalSeamTrace R (fkRectConfigurationToMedialPairing R omega) d (orderOf (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalOrbitWalk_winding R omega d

/--
[fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectRefinedBoundaryOrbitTranslation (fkRectConfigurationToMedialPairing R omega) d (fkRectRefinedBoundaryCanonicalCenter R d) = (4 * (fkRectSquareDeckTranslation R (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1, 4 * (fkRectSquareDeckTranslation R (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding R omega d

/--
[fkRectRefinedBoundaryOrbit_exists_canonicalWindingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryOrbit_exists_canonicalWindingWitness_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  Nonempty (FKRectSquareCoverCycleWitness R (4 * (fkRectSquareDeckTranslation R (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1, 4 * (fkRectSquareDeckTranslation R (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryOrbit_exists_canonicalWindingWitness R omega d

/--
[fkRectRefinedBoundaryOrbit_exists_largeCanonicalWindingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryOrbit_exists_largeCanonicalWindingWitness_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  Nonempty (FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R) (4 * (fkRectSquareDeckTranslation R (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1, 4 * (fkRectSquareDeckTranslation R (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryOrbit_exists_largeCanonicalWindingWitness R omega d

/--
[fkRectMedialBoundaryPrimalOrbitWalk_windingIndependent_of_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalOrbitWalk_windingIndependent_of_intersection_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
  {C : FKRectSquareCoverCycleWitness R (fkRectRefinedBoundaryOrbitTranslation (fkRectConfigurationToMedialPairing R omega) d (fkRectRefinedBoundaryCanonicalCenter R d))}
  {D : FKRectSquareCoverCycleWitness R (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1, 4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)}
-- given
  (hw : FKRectSquareWalkLift R w p q)
  (hne : C.cycle.intersection D.cycle ≠ 0) :
-- imply
  FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d)) (fkRectWalkWinding R w) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalOrbitWalk_windingIndependent_of_intersection R omega d hw C D hne

/--
[fkRectMedialBoundaryPrimalOrbitWalk_windingIndependent_of_largeIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalOrbitWalk_windingIndependent_of_largeIntersection_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
  {C : FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R) (fkRectRefinedBoundaryOrbitTranslation (fkRectConfigurationToMedialPairing R omega) d (fkRectRefinedBoundaryCanonicalCenter R d))}
  {D : FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R) (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1, 4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)}
-- given
  (hw : FKRectSquareWalkLift R w p q)
  (hne : C.cycle.intersection D.cycle ≠ 0) :
-- imply
  FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d)) (fkRectWalkWinding R w) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalOrbitWalk_windingIndependent_of_largeIntersection R omega d hw C D hne


-- created on 2026-10-23
