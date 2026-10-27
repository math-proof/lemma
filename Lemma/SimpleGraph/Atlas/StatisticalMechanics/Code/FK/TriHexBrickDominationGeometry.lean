import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDominationGeometry
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexBrickInnerFaceMap_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDominationGeometry.lean)
-/
@[path]
private lemma triHexBrickInnerFaceMap_adjMatch_eq
  {N m : Nat}
-- given
  (hNm : N < m) :
-- imply
  ocd_AdjMatch (triHexBrickInnerTriangleGraph N) (triHexBrickFullDualGraph m) (triHexBrickInnerFaceMap N m) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickInnerFaceMap_adjMatch hNm

/--
[triHexBrickInner_boundary_of_outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDominationGeometry.lean)
-/
@[path]
private lemma triHexBrickInner_boundary_of_outsideGraph_adj_eq
  {N m : Nat}
  {psi : ConfigSpace (Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m)))}
  {x : {z : Site 2 // z ∈ box 2 N}}
  {C : kwg_Face (triHexPlanarFiniteStarPlanar m)}
-- given
  (hNm : N < m)
  (hN : 1 ≤ N)
  (h : (ocd_outsideGraph (triHexBrickFullDualGraph m) (triHexBrickInnerFaceMap N m) (fun _ => False) psi).Adj (triHexBrickInnerFaceMap N m x) C) :
-- imply
  triHexBrickInnerBoundary N x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickInner_boundary_of_outsideGraph_adj hNm hN psi h

/--
[triHexBrickInner_inducedWiring_le_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDominationGeometry.lean)
-/
@[path]
private lemma triHexBrickInner_inducedWiring_le_boundaryClique_eq
  {N m : Nat}
  {psi : ConfigSpace (Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m)))}
-- given
  (hNm : N < m)
  (hN : 1 ≤ N) :
-- imply
  ocd_inducedWiring (triHexBrickFullDualGraph m) (triHexBrickInnerFaceMap N m) (fun _ => False) psi ≤ boundaryCliqueGraph (triHexBrickInnerBoundary N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickInner_inducedWiring_le_boundaryClique hNm hN psi


-- created on 2026-10-23
