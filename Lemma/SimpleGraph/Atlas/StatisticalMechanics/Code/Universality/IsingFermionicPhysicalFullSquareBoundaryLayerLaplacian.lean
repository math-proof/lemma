import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
open StatMech StatMech.Universality


/--
[fkIsingSquareBoundaryFullVertexFullObservable_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryFullVertexFullObservable_quad_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hn : 0 < n)
  (heast : fkIsingSquareDirectionAvailable n x .east)
  (hnorth : fkIsingSquareDirectionAvailable n x .north)
  (hwest : fkIsingSquareDirectionAvailable n x .west)
  (hsouth : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareBoundaryFullMedialObservable n hn (boundaryVertexEdge n x .south hsouth)) (fkIsingSquareBoundaryFullMedialObservable n hn (boundaryVertexEdge n x .west hwest)) (fkIsingSquareBoundaryFullMedialObservable n hn (boundaryVertexEdge n x .north hnorth)) (fkIsingSquareBoundaryFullMedialObservable n hn (boundaryVertexEdge n x .east heast)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryFullVertexFullObservable_quad n hn x heast hnorth hwest hsouth


-- created on 2026-10-23
