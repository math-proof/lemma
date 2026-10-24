import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoordinates
open Finset Set SimpleGraph StatMech StatMech.FrontierD


/--
[kwg_embeddedEdge_eq_sharedPrimalEdge_of_dualEnds_eq_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoordinates.lean)
-/
@[path]
private lemma kwg_embeddedEdge_eq_sharedPrimalEdge_of_dualEnds_eq_inner_eq
  {N m : Nat}
  {x y : FK.boxVerts 2 N}
  {e : kwg_Edge (fkSquareBoxPlanar m)}
-- given
  (hNm : N < m)
  (hxy : (FK.boxGraph 2 N).Adj x y)
  (he : kwg_dualEnds (fkSquareBoxPlanar m) e = s(fkSquareBox_innerFaceMap N m x, fkSquareBox_innerFaceMap N m y)) :
-- imply
  kwg_embeddedEdge (fkSquareBoxPlanar m) e = sharedPrimalEdge x.1 y.1 := by
-- proof
  apply StatMech.FrontierD.kwg_embeddedEdge_eq_sharedPrimalEdge_of_dualEnds_eq_inner hNm hxy he

/--
[fkSquareDualInnerActiveRestrict_pfdSupport_eq_faceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoordinates.lean)
-/
@[path]
private lemma fkSquareDualInnerActiveRestrict_pfdSupport_eq_faceDual_eq
  {N m : Nat}
  {omega : ConfigSpace (Sym2 (FK.boxVerts 2 m))}
-- given
  (hNm : N < m) :
-- imply
  fkSquareDualInnerActiveRestrict hNm (fkSquarePfdSupport m omega) = fkSquareFaceDualInnerActive N (FK.extendEdge 2 m omega) := by
-- proof
  apply StatMech.FrontierD.fkSquareDualInnerActiveRestrict_pfdSupport_eq_faceDual hNm omega

/--
[fkSquare_innerEdgeLE_mem_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoordinates.lean)
-/
@[path]
private lemma fkSquare_innerEdgeLE_mem_edgeSet_eq
  {R N : Nat}
  {a : (FK.boxGraph 2 R).edgeSet}
-- given
  (hRN : R ≤ N) :
-- imply
  FK.innerEdgeLE 2 hRN a.1 ∈ (FK.boxGraph 2 N).edgeSet := by
-- proof
  apply StatMech.FrontierD.fkSquare_innerEdgeLE_mem_edgeSet hRN a

/--
[fkSquareActiveRestrictLE_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoordinates.lean)
-/
@[path]
private lemma fkSquareActiveRestrictLE_monotone_eq
  {R N : Nat}
-- given
  (hRN : R ≤ N) :
-- imply
  Monotone (fkSquareActiveRestrictLE hRN) := by
-- proof
  apply StatMech.FrontierD.fkSquareActiveRestrictLE_monotone hRN

/--
[fkSquareActiveRestrictLE_faceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoordinates.lean)
-/
@[path]
private lemma fkSquareActiveRestrictLE_faceDual_eq
  {R N : Nat}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hRN : R ≤ N) :
-- imply
  fkSquareActiveRestrictLE hRN (fkSquareFaceDualInnerActive N omega) = fkSquareFaceDualInnerActive R omega := by
-- proof
  apply StatMech.FrontierD.fkSquareActiveRestrictLE_faceDual hRN omega

/--
[fkSquareActiveRestrictLE_restrictActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoordinates.lean)
-/
@[path]
private lemma fkSquareActiveRestrictLE_restrictActive_eq
  {R N : Nat}
  {eta : ConfigSpace (Sym2 (FK.boxVerts 2 N))}
-- given
  (hRN : R ≤ N) :
-- imply
  fkSquareActiveRestrictLE hRN (restrictActive (FK.boxGraph 2 N) eta) = restrictActive (FK.boxGraph 2 R) (FK.boxRestrictLE 2 hRN eta) := by
-- proof
  apply StatMech.FrontierD.fkSquareActiveRestrictLE_restrictActive hRN eta


-- created on 2026-10-23
