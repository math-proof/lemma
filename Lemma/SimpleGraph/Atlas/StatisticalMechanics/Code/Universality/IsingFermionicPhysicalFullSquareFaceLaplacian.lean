import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareFullIntegratedPrimitive


/--
[fkIsingSquareFullFaceFullObservable_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean)
-/
@[path]
private lemma fkIsingSquareFullFaceFullObservable_quad_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareWiredFullMedialObservable n hn (faceNorthEdge n c)) (fkIsingSquareWiredFullMedialObservable n hn (faceEastEdge n c)) (fkIsingSquareWiredFullMedialObservable n hn (faceSouthEdge n c)) (fkIsingSquareWiredFullMedialObservable n hn (faceWestEdge n c)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullFaceFullObservable_quad n hn c

/--
[fkIsingSquareFullFace_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean)
-/
@[path]
private lemma fkIsingSquareFullFace_neighborFinset_eq
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
  apply StatMech.Universality.fkIsingSquareFullFace_neighborFinset n c heast hnorth hwest hsouth

/--
[face_laplacian_nonneg_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean)
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
  0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn) c := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullIntegratedPrimitive.face_laplacian_nonneg_of_interior n hn c heast hnorth hwest hsouth


-- created on 2026-10-23
