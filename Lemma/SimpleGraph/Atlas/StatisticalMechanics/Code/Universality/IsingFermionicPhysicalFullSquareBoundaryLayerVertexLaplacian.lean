import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerVertexIntegratedPrimitive


/--
[vertex_difference_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.lean)
-/
@[path]
private lemma vertex_difference_north_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hn : 0 < n)
  (hnorth : fkIsingSquareDirectionAvailable n x .north)
  (hwest : fkIsingSquareDirectionAvailable n x .west) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareNeighbor n x .north hnorth) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fullVertexNorthEdge n x hnorth, .west)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fullVertexNorthEdge n x hnorth, .north)) := by
-- proof
  apply StatMech.Universality.vertex_difference_north n hn x hnorth hwest

/--
[vertex_difference_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.lean)
-/
@[path]
private lemma vertex_difference_east_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hn : 0 < n)
  (heast : fkIsingSquareDirectionAvailable n x .east)
  (hnorth : fkIsingSquareDirectionAvailable n x .north) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareNeighbor n x .east heast) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fullVertexEastEdge n x heast, .west)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fullVertexEastEdge n x heast, .north)) := by
-- proof
  apply StatMech.Universality.vertex_difference_east n hn x heast hnorth

/--
[vertex_difference_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.lean)
-/
@[path]
private lemma vertex_difference_south_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hn : 0 < n)
  (hsouth : fkIsingSquareDirectionAvailable n x .south)
  (heast : fkIsingSquareDirectionAvailable n x .east) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareNeighbor n x .south hsouth) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fullVertexSouthEdge n x hsouth, .east)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fullVertexSouthEdge n x hsouth, .south)) := by
-- proof
  apply StatMech.Universality.vertex_difference_south n hn x hsouth heast

/--
[vertex_difference_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.lean)
-/
@[path]
private lemma vertex_difference_west_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareDirectionAvailable n x .west)
  (hsouth : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareNeighbor n x .west hwest) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fullVertexWestEdge n x hwest, .east)) - fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fullVertexWestEdge n x hwest, .south)) := by
-- proof
  apply StatMech.Universality.vertex_difference_west n hn x hwest hsouth

/--
[vertex_laplacian_nonpos_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.lean)
-/
@[path]
private lemma vertex_laplacian_nonpos_of_interior_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hn : 0 < n)
  (heast : fkIsingSquareDirectionAvailable n x .east)
  (hnorth : fkIsingSquareDirectionAvailable n x .north)
  (hwest : fkIsingSquareDirectionAvailable n x .west)
  (hsouth : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive) x ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerVertexIntegratedPrimitive.vertex_laplacian_nonpos_of_interior n hn x heast hnorth hwest hsouth


-- created on 2026-10-23
