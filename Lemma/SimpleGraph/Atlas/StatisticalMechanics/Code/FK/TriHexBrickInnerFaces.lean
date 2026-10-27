import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickInnerFaces.Part3
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexBrickInner_faceRegion_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean)
-/
@[path]
private lemma triHexBrickInner_faceRegion_adj_iff_eq
  {N m : Nat}
  {f g : Site 2}
-- given
  (hNm : N < m)
  (t : {z : Site 2 // z ∈ box 2 N})
  (hf : f = hexagonalBrickFaceLeft t.1 ∨ f = hexagonalBrickFaceRight t.1) :
-- imply
  (whb_faceRegion (imageGraph (triHexPlanarFiniteStarPlanar m))).Adj f g ↔ (f = hexagonalBrickFaceLeft t.1 ∧ g = hexagonalBrickFaceRight t.1) ∨ (f = hexagonalBrickFaceRight t.1 ∧ g = hexagonalBrickFaceLeft t.1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickInner_faceRegion_adj_iff hNm t f g hf

/--
[triHexPlanarFiniteStar_pfdFace_eq_inner_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_pfdFace_eq_inner_iff_eq
  {N m : Nat}
  {f : Site 2}
-- given
  (hNm : N < m)
  (t : {z : Site 2 // z ∈ box 2 N}) :
-- imply
  BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar m) f = triHexPlanarFiniteStarFace m t.1 ↔ f = hexagonalBrickFaceLeft t.1 ∨ f = hexagonalBrickFaceRight t.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_pfdFace_eq_inner_iff hNm t f

/--
[triHexBrickInnerFaceMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean)
-/
@[path]
private lemma triHexBrickInnerFaceMap_injective_eq
  {N m : Nat}
-- given
  (hNm : N < m) :
-- imply
  Function.Injective (triHexBrickInnerFaceMap N m) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickInnerFaceMap_injective hNm

/--
[triHexPlanarFiniteStarFace_eq_inner_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarFace_eq_inner_iff_eq
  {N m : Nat}
  {u : Site 2}
-- given
  (hNm : N < m)
  (t : {z : Site 2 // z ∈ box 2 N}) :
-- imply
  triHexPlanarFiniteStarFace m u = triHexPlanarFiniteStarFace m t.1 ↔ u = t.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarFace_eq_inner_iff hNm t u

/--
[triHexSpokeFaces_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean)
-/
@[path]
private lemma triHexSpokeFaces_adj_eq
  {z : Site 2}
  {i : Fin 3} :
-- imply
  triangularGraph.Adj (triHexSpokeFace1 z i) (triHexSpokeFace2 z i) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexSpokeFaces_adj z i

/--
[triHexBrickInnerFaceMap_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean)
-/
@[path]
private lemma triHexBrickInnerFaceMap_adj_eq
  {N m : Nat}
-- given
  (hNm : N < m)
  (x y : {z : Site 2 // z ∈ box 2 N}) :
-- imply
  (triHexBrickInnerTriangleGraph N).Adj x y ↔ (triHexBrickFullDualGraph m).Adj (triHexBrickInnerFaceMap N m x) (triHexBrickInnerFaceMap N m y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickInnerFaceMap_adj hNm x y


-- created on 2026-10-23
