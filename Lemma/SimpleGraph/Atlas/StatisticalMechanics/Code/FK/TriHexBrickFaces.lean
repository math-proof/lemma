import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexBrickFaces
open SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[hexagonalBrickFaces_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma hexagonalBrickFaces_adj_eq
  {t : Site 2} :
-- imply
  (hypercubicLattice 2).Adj (hexagonalBrickFaceLeft t) (hexagonalBrickFaceRight t) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBrickFaces_adj t

/--
[hexagonalBrickFaces_shared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma hexagonalBrickFaces_shared_eq
  {t : Site 2} :
-- imply
  sharedPrimalEdge (hexagonalBrickFaceLeft t) (hexagonalBrickFaceRight t) = s(hexagonalBrickVertex (t + hexagonalStep 1, true), hexagonalBrickVertex (t - hexagonalStep 1, false)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBrickFaces_shared t

/--
[hexagonalBrickFaces_middle_not_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma hexagonalBrickFaces_middle_not_adj_eq
  {t : Site 2} :
-- imply
  ¬ hexagonalGraph.Adj (t + hexagonalStep 1, true) (t - hexagonalStep 1, false) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBrickFaces_middle_not_adj t

/--
[triHexPlanarFiniteStar_middle_not_mem_imageGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_middle_not_mem_imageGraph_eq
  {n : Nat}
  {t : Site 2} :
-- imply
  sharedPrimalEdge (hexagonalBrickFaceLeft t) (hexagonalBrickFaceRight t) ∉ (imageGraph (triHexPlanarFiniteStarPlanar n)).edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_middle_not_mem_imageGraph n t

/--
[triHexPlanarFiniteStar_pfdFace_left_eq_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_pfdFace_left_eq_right_eq
  {n : Nat}
  {t : Site 2} :
-- imply
  BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n) (hexagonalBrickFaceLeft t) = BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n) (hexagonalBrickFaceRight t) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_pfdFace_left_eq_right n t

/--
[triHexPlanarFiniteStarFace_eq_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarFace_eq_right_eq
  {n : Nat}
  {t : Site 2} :
-- imply
  triHexPlanarFiniteStarFace n t = BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n) (hexagonalBrickFaceRight t) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarFace_eq_right n t

/--
[triHexBrickSpokeFlanks_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexBrickSpokeFlanks_adj_eq
  {z : Site 2}
  {i : Fin 3} :
-- imply
  (hypercubicLattice 2).Adj (triHexBrickSpokeFlank1 z i) (triHexBrickSpokeFlank2 z i) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickSpokeFlanks_adj z i

/--
[triHexBrickSpokeFlanks_shared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexBrickSpokeFlanks_shared_eq
  {z : Site 2}
  {i : Fin 3} :
-- imply
  sharedPrimalEdge (triHexBrickSpokeFlank1 z i) (triHexBrickSpokeFlank2 z i) = s(hexagonalBrickVertex (z, false), hexagonalBrickVertex (z + hexagonalStep i, true)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickSpokeFlanks_shared z i

/--
[triHexBrickSpokeFlank1_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexBrickSpokeFlank1_face_eq
  {n : Nat}
  {z : Site 2}
  {i : Fin 3} :
-- imply
  BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n) (triHexBrickSpokeFlank1 z i) = triHexPlanarFiniteStarFace n (triHexSpokeFace1 z i) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickSpokeFlank1_face n z i

/--
[triHexBrickSpokeFlank2_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexBrickSpokeFlank2_face_eq
  {n : Nat}
  {z : Site 2}
  {i : Fin 3} :
-- imply
  BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n) (triHexBrickSpokeFlank2 z i) = triHexPlanarFiniteStarFace n (triHexSpokeFace2 z i) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickSpokeFlank2_face n z i

/--
[triHexPlanarFiniteStar_embeddedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_embeddedEdge_eq
  {n : Nat}
  {z : TriHexPlanarFiniteCell n}
  {i : Fin 3} :
-- imply
  kwg_embeddedEdge (triHexPlanarFiniteStarPlanar n) (triHexPlanarFiniteStarEdgeEquiv n (z, i)) = s(hexagonalBrickVertex (z.1, false), hexagonalBrickVertex (z.1 + hexagonalStep i, true)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_embeddedEdge n z i

/--
[triHexPlanarFiniteStar_embeddedEdge_mem_imageGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_embeddedEdge_mem_imageGraph_eq
  {n : Nat}
  {z : TriHexPlanarFiniteCell n}
  {i : Fin 3} :
-- imply
  kwg_embeddedEdge (triHexPlanarFiniteStarPlanar n) (triHexPlanarFiniteStarEdgeEquiv n (z, i)) ∈ (imageGraph (triHexPlanarFiniteStarPlanar n)).edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_embeddedEdge_mem_imageGraph n z i

/--
[triHexBrickSpokeFlanks_shared_mem_imageGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexBrickSpokeFlanks_shared_mem_imageGraph_eq
  {n : Nat}
  {z : TriHexPlanarFiniteCell n}
  {i : Fin 3} :
-- imply
  sharedPrimalEdge (triHexBrickSpokeFlank1 z.1 i) (triHexBrickSpokeFlank2 z.1 i) ∈ (imageGraph (triHexPlanarFiniteStarPlanar n)).edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickSpokeFlanks_shared_mem_imageGraph n z i

/--
[triHexPlanarFiniteStar_dualEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_dualEnds_eq
  {n : Nat}
  {z : TriHexPlanarFiniteCell n}
  {i : Fin 3} :
-- imply
  kwg_dualEnds (triHexPlanarFiniteStarPlanar n) (triHexPlanarFiniteStarEdgeEquiv n (z, i)) = s(triHexPlanarFiniteStarFace n (triHexSpokeFace1 z.1 i), triHexPlanarFiniteStarFace n (triHexSpokeFace2 z.1 i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_dualEnds n z i


-- created on 2026-10-23
