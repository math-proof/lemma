import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualCoordinates.Part4
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexPlanarFiniteStarEdgeIncl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarEdgeIncl_injective_eq
  {m : Nat} :
-- imply
  Function.Injective (triHexPlanarFiniteStarEdgeIncl m) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarEdgeIncl_injective m

/--
[triHexPlanarFiniteStarExtendEdge_edgeIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarExtendEdge_edgeIncl_eq
  {m : Nat}
  {omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V)}
  {e : Sym2 (triHexPlanarFiniteStarPlanar m).V} :
-- imply
  triHexPlanarFiniteStarExtendEdge m omega (triHexPlanarFiniteStarEdgeIncl m e) = omega e := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarExtendEdge_edgeIncl m omega e

/--
[monotone_triHexPlanarFiniteStarExtendEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean)
-/
@[path]
private lemma monotone_triHexPlanarFiniteStarExtendEdge_eq
  {m : Nat} :
-- imply
  Monotone (triHexPlanarFiniteStarExtendEdge m) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.monotone_triHexPlanarFiniteStarExtendEdge m

/--
[continuous_triHexFaceDualInnerActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean)
-/
@[path]
private lemma continuous_triHexFaceDualInnerActive_eq
  {N : Nat} :
-- imply
  Continuous (triHexFaceDualInnerActive N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.continuous_triHexFaceDualInnerActive N

/--
[antitone_triHexFaceDualInnerActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean)
-/
@[path]
private lemma antitone_triHexFaceDualInnerActive_eq
  {N : Nat} :
-- imply
  Antitone (triHexFaceDualInnerActive N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.antitone_triHexFaceDualInnerActive N

/--
[isClopen_triHexFaceDualInnerEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean)
-/
@[path]
private lemma isClopen_triHexFaceDualInnerEvent_eq
  {N : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)} :
-- imply
  IsClopen (triHexFaceDualInnerEvent N A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.isClopen_triHexFaceDualInnerEvent N A

/--
[triHexFaceDualInnerEvent_isDecreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean)
-/
@[path]
private lemma triHexFaceDualInnerEvent_isDecreasing_eq
  {N : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsDecreasing (triHexFaceDualInnerEvent N A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFaceDualInnerEvent_isDecreasing N hA

/--
[triHexPlanarFiniteStar_edgeIncl_eq_fullDual_of_dualEnds_eq_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_edgeIncl_eq_fullDual_of_dualEnds_eq_inner_eq
  {N m : Nat}
  {x y : TriangularBoxVertex N}
  {e : kwg_Edge (triHexPlanarFiniteStarPlanar m)}
-- given
  (hNm : N < m)
  (he : kwg_dualEnds (triHexPlanarFiniteStarPlanar m) e = s(triHexBrickInnerFaceMap N m x, triHexBrickInnerFaceMap N m y)) :
-- imply
  triHexPlanarFiniteStarEdgeIncl m e.1 = triHexFullDualEdgeEquiv s(x.1, y.1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_edgeIncl_eq_fullDual_of_dualEnds_eq_inner hNm he

/--
[triHexBrickDualInnerActiveRestrict_pfdSupport_eq_faceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean)
-/
@[path]
private lemma triHexBrickDualInnerActiveRestrict_pfdSupport_eq_faceDual_eq
  {N m : Nat}
  {omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V)}
-- given
  (hNm : N < m) :
-- imply
  triHexBrickDualInnerActiveRestrict hNm (triHexBrickPfdSupport m omega) = triHexFaceDualInnerActive N (triHexPlanarFiniteStarExtendEdge m omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickDualInnerActiveRestrict_pfdSupport_eq_faceDual hNm omega


-- created on 2026-10-23
