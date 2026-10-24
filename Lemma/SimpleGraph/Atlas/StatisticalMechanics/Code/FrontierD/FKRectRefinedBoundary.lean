import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary
open StatMech StatMech.FrontierD


/--
[fkMedialLocalMate_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkMedialLocalMate_side_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  (fkMedialLocalMate pairing d).2 = fkRectMedialLocalMateSide (pairing d.1) d.2 := by
-- proof
  apply StatMech.FrontierD.fkMedialLocalMate_side pairing d

/--
[fkRectRefinedDartPoint_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectRefinedDartPoint_bondMate_eq
  {T : EvenTorus}
  {c : Int × Int}
  {d : FKMedialDart T} :
-- imply
  fkRectRefinedDartPoint (fkRectRefinedBondCenter c d.2) (fkMedialBondMate T d).2 = fkRectRefinedDartPoint c d.2 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDartPoint_bondMate T c d

/--
[fkRectRefinedLocalDarts_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectRefinedLocalDarts_path_eq
  {pairing : Bool}
  {c : Int × Int}
  {side : FKMedialSide} :
-- imply
  FKRectIntegralSquareDartPath (fkRectRefinedDartPoint c side) (fkRectRefinedDartPoint c (fkRectMedialLocalMateSide pairing side)) (fkRectRefinedLocalDarts pairing c side) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedLocalDarts_path pairing c side

/--
[fkRectRefinedBoundaryDarts_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryDarts_path_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T}
  {c : Int × Int}
  {n : Nat} :
-- imply
  FKRectIntegralSquareDartPath (fkRectRefinedDartPoint c d.2) (fkRectRefinedDartPoint (fkRectRefinedBoundaryCenterAfter pairing d c n) (((fkMedialBoundaryStep pairing)^[n] d).2)) (fkRectRefinedBoundaryDarts pairing d c n) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryDarts_path pairing d c n

/--
[fkRectRefinedBoundaryOrbitDarts_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryOrbitDarts_path_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T}
  {c : Int × Int} :
-- imply
  FKRectIntegralSquareDartPath (fkRectRefinedDartPoint c d.2) (fkRectRefinedDartPoint (fkRectRefinedBoundaryCenterAfter pairing d c (orderOf (fkMedialBoundaryStep pairing))) d.2) (fkRectRefinedBoundaryDarts pairing d c (orderOf (fkMedialBoundaryStep pairing))) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryOrbitDarts_path pairing d c

/--
[fkRectCanonicalSquareEdgeStep_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectCanonicalSquareEdgeStep_eq_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2 - fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1 = if fkRectClosedPairingAtEdge e then (-1, 0) else (0, 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalSquareEdgeStep_eq R e

/--
[fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  if fkRectClosedPairingAtEdge e then fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1 = fkRectMedialEastPrimal R e ∧ fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2 = fkRectMedialWestPrimal R e else fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1 = fkRectMedialWestPrimal R e ∧ fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2 = fkRectMedialEastPrimal R e := by
-- proof
  apply StatMech.FrontierD.fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation R e

/--
[fkRectRefinedFourEast_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectRefinedFourEast_path_eq
  {p : Int × Int} :
-- imply
  FKRectIntegralSquareDartPath p (p.1 + 4, p.2) [(p, 0), ((p.1 + 1, p.2), 0), ((p.1 + 2, p.2), 0), ((p.1 + 3, p.2), 0)] := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedFourEast_path p

/--
[fkRectRefinedFourWest_path_public](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectRefinedFourWest_path_public_eq
  {p : Int × Int} :
-- imply
  FKRectIntegralSquareDartPath p (p.1 - 4, p.2) [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2), ((p.1 - 3, p.2), 2)] := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedFourWest_path_public p

/--
[fkRectRefinedFourNorth_path_public](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectRefinedFourNorth_path_public_eq
  {p : Int × Int} :
-- imply
  FKRectIntegralSquareDartPath p (p.1, p.2 + 4) [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1), ((p.1, p.2 + 3), 1)] := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedFourNorth_path_public p

/--
[fkRectRefinedFourSouth_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectRefinedFourSouth_path_eq
  {p : Int × Int} :
-- imply
  FKRectIntegralSquareDartPath p (p.1, p.2 - 4) [(p, 3), ((p.1, p.2 - 1), 3), ((p.1, p.2 - 2), 3), ((p.1, p.2 - 3), 3)] := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedFourSouth_path p

/--
[fkRectRefinedPrimalEdgeDarts_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean)
-/
@[path]
private lemma fkRectRefinedPrimalEdgeDarts_path_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  FKRectIntegralSquareDartPath (fkRectRefinedPrimalEdgeStart R e) (fkRectRefinedPrimalEdgeEnd R e) (fkRectRefinedPrimalEdgeDarts R e) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedPrimalEdgeDarts_path R e


-- created on 2026-10-23
