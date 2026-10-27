import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerIntegratedPrimitive


/--
[faceWestEdge_eq_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma faceWestEdge_eq_south_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  faceWestEdge n c = fkIsingSquareDirectionEdge n (faceNWVertex n c) .south (faceNW_south_available n c) := by
-- proof
  apply StatMech.Universality.faceWestEdge_eq_south n c

/--
[faceNorthEdge_eq_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma faceNorthEdge_eq_west_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  faceNorthEdge n c = fkIsingSquareDirectionEdge n (faceNEVertex n c) .west (faceNE_west_available n c) := by
-- proof
  apply StatMech.Universality.faceNorthEdge_eq_west n c

/--
[faceEastEdge_eq_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma faceEastEdge_eq_south_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  faceEastEdge n c = fkIsingSquareDirectionEdge n (faceNEVertex n c) .south (faceNE_south_available n c) := by
-- proof
  apply StatMech.Universality.faceEastEdge_eq_south n c

/--
[faceSouthEdge_eq_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma faceSouthEdge_eq_west_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  faceSouthEdge n c = fkIsingSquareDirectionEdge n (faceSEVertex n c) .west (faceSE_west_available n c) := by
-- proof
  apply StatMech.Universality.faceSouthEdge_eq_west n c

/--
[faceSouthWest_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma faceSouthWest_bondMate_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondMate n hn (faceSouthWestDart n c).1 = (faceWestEdge n c, .south) := by
-- proof
  apply StatMech.Universality.faceSouthWest_bondMate n hn c

/--
[faceWestEast_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma faceWestEast_bondMate_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondMate n hn (faceWestEastDart n c).1 = (faceNorthEdge n c, .south) := by
-- proof
  apply StatMech.Universality.faceWestEast_bondMate n hn c

/--
[faceNorthEast_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma faceNorthEast_bondMate_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondMate n hn (faceNorthEastDart n c).1 = (faceEastEdge n c, .north) := by
-- proof
  apply StatMech.Universality.faceNorthEast_bondMate n hn c

/--
[faceEastWest_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma faceEastWest_bondMate_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondMate n hn (faceEastWestDart n c).1 = (faceSouthEdge n c, .north) := by
-- proof
  apply StatMech.Universality.faceEastWest_bondMate n hn c

/--
[fkIsingSquareBoundaryFullFaceFullObservable_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryFullFaceFullObservable_quad_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hN : (faceNorthEdge n c).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
  (hE : (faceEastEdge n c).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
  (hS : (faceSouthEdge n c).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
  (hW : (faceWestEdge n c).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryFullMedialObservable n hn (faceNorthEdge n c)) (fkIsingSquareBoundaryFullMedialObservable n hn (faceEastEdge n c)) (fkIsingSquareBoundaryFullMedialObservable n hn (faceSouthEdge n c)) (fkIsingSquareBoundaryFullMedialObservable n hn (faceWestEdge n c)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryFullFaceFullObservable_quad n hn c hN hE hS hW

/--
[fkIsingSquareBoundaryFullFace_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryFullFace_neighborFinset_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
  [Fintype ↑((fkIsingSquareFullFaceGraph n).neighborSet c)]
-- given
  (heast : c.1.1 + 1 < 2 * n)
  (hnorth : c.2.1 + 1 < 2 * n)
  (hwest : 0 < c.1.1)
  (hsouth : 0 < c.2.1) :
-- imply
  (fkIsingSquareFullFaceGraph n).neighborFinset c = {faceEastNeighbor n c heast, faceNorthNeighbor n c hnorth, faceWestNeighbor n c hwest, faceSouthNeighbor n c hsouth} := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryFullFace_neighborFinset n c heast hnorth hwest hsouth

/--
[face_difference_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma face_difference_north_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hnorth : c.2.1 + 1 < 2 * n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (faceNorthNeighbor n c hnorth) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (faceNorthEdge n c, .north)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (faceNorthEdge n c, .east)) := by
-- proof
  apply StatMech.Universality.face_difference_north n hn c hnorth

/--
[face_difference_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma face_difference_east_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (heast : c.1.1 + 1 < 2 * n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (faceEastNeighbor n c heast) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (faceEastEdge n c, .south)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (faceEastEdge n c, .west)) := by
-- proof
  apply StatMech.Universality.face_difference_east n hn c heast

/--
[face_difference_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma face_difference_south_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hsouth : 0 < c.2.1) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (faceSouthNeighbor n c hsouth) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (faceSouthEdge n c, .south)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (faceSouthEdge n c, .west)) := by
-- proof
  apply StatMech.Universality.face_difference_south n hn c hsouth

/--
[face_difference_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma face_difference_west_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (hwest : 0 < c.1.1) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (faceWestNeighbor n c hwest) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (faceWestEdge n c, .north)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (faceWestEdge n c, .east)) := by
-- proof
  apply StatMech.Universality.face_difference_west n hn c hwest

/--
[face_laplacian_nonneg_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean)
-/
@[path]
private lemma face_laplacian_nonneg_of_interior_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (heast : c.1.1 + 1 < 2 * n)
  (hnorth : c.2.1 + 1 < 2 * n)
  (hwest : 0 < c.1.1)
  (hsouth : 0 < c.2.1) :
-- imply
  0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive) c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerIntegratedPrimitive.face_laplacian_nonneg_of_interior n hn c heast hnorth hwest hsouth


-- created on 2026-10-23
