import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareFullIntegratedPrimitive


/--
[fkIsingSquareFullVertexFullObservable_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareLaplacian.lean)
-/
@[path]
private lemma fkIsingSquareFullVertexFullObservable_quad_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hn : 0 < n)
  (heast : fkIsingSquareDirectionAvailable n x .east)
  (hnorth : fkIsingSquareDirectionAvailable n x .north)
  (hwest : fkIsingSquareDirectionAvailable n x .west)
  (hsouth : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareWiredFullMedialObservable n hn (fullVertexSouthEdge n x hsouth)) (fkIsingSquareWiredFullMedialObservable n hn (fullVertexWestEdge n x hwest)) (fkIsingSquareWiredFullMedialObservable n hn (fullVertexNorthEdge n x hnorth)) (fkIsingSquareWiredFullMedialObservable n hn (fullVertexEastEdge n x heast)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullVertexFullObservable_quad n hn x heast hnorth hwest hsouth

/--
[fkIsingSquareFullVertex_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareLaplacian.lean)
-/
@[path]
private lemma fkIsingSquareFullVertex_neighborFinset_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (heast : fkIsingSquareDirectionAvailable n x .east)
  (hnorth : fkIsingSquareDirectionAvailable n x .north)
  (hwest : fkIsingSquareDirectionAvailable n x .west)
  (hsouth : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  (fkSquareBoxPlanar n).G.neighborFinset x = {fkIsingSquareNeighbor n x .east heast, fkIsingSquareNeighbor n x .north hnorth, fkIsingSquareNeighbor n x .west hwest, fkIsingSquareNeighbor n x .south hsouth} := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullVertex_neighborFinset n x heast hnorth hwest hsouth

/--
[vertex_laplacian_nonpos_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareLaplacian.lean)
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
  isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn) x ≤ 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.vertex_laplacian_nonpos_of_interior n hn x heast hnorth hwest hsouth


-- created on 2026-10-23
