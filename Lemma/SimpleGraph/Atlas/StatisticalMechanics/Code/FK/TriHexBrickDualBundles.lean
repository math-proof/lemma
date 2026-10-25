import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualBundles
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexSpokeFaces_eq_triangularIndexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualBundles.lean)
-/
@[path]
private lemma triHexSpokeFaces_eq_triangularIndexedEdge_eq
  {z : Site 2}
  {i : Fin 3} :
-- imply
  s(triHexSpokeFace1 z i, triHexSpokeFace2 z i) = triangularIndexedEdge (triHexIndexEquiv.symm (z, i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexSpokeFaces_eq_triangularIndexedEdge z i

/--
[triHexBrick_edge_eq_of_dualEnds_eq_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualBundles.lean)
-/
@[path]
private lemma triHexBrick_edge_eq_of_dualEnds_eq_inner_eq
  {N m : Nat}
  {x y : {z : Site 2 // z ∈ box 2 N}}
  {e f : kwg_Edge (triHexPlanarFiniteStarPlanar m)}
-- given
  (hNm : N < m)
  (he : kwg_dualEnds (triHexPlanarFiniteStarPlanar m) e = s(triHexBrickInnerFaceMap N m x, triHexBrickInnerFaceMap N m y))
  (hf : kwg_dualEnds (triHexPlanarFiniteStarPlanar m) f = s(triHexBrickInnerFaceMap N m x, triHexBrickInnerFaceMap N m y)) :
-- imply
  e = f := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_edge_eq_of_dualEnds_eq_inner hNm he hf

/--
[triHexBrick_pfdEdgeBundle_inner_card_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualBundles.lean)
-/
@[path]
private lemma triHexBrick_pfdEdgeBundle_inner_card_eq_one_eq
  {N m : Nat}
  {a : (triHexBrickInnerTriangleGraph N).edgeFinset}
-- given
  (hNm : N < m) :
-- imply
  (pfdEdgeBundle (triHexPlanarFiniteStarPlanar m) (ocd_innerEdge (triHexBrickInnerFaceMap N m) a.1)).card = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_pfdEdgeBundle_inner_card_eq_one hNm a

/--
[triHexBrick_pfdEffectiveParam_innerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualBundles.lean)
-/
@[path]
private lemma triHexBrick_pfdEffectiveParam_innerEdge_eq
  {N m : Nat}
  {p : Real}
  {a : (triHexBrickInnerTriangleGraph N).edgeFinset}
-- given
  (hNm : N < m) :
-- imply
  pfdEffectiveParam (triHexPlanarFiniteStarPlanar m) p (ocd_innerEdge (triHexBrickInnerFaceMap N m) a.1) = p := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_pfdEffectiveParam_innerEdge hNm p a


-- created on 2026-10-23
