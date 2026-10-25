import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualBundles.Part2
open Finset Set SimpleGraph StatMech StatMech.FrontierD


/--
[mem_pfdEdgeBundle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualBundles.lean)
-/
@[path]
private lemma mem_pfdEdgeBundle_eq
  {P : PlanarZ2Subgraph}
  {a : Sym2 (kwg_Face P)}
  {e : kwg_Edge P} :
-- imply
  e ∈ pfdEdgeBundle P a ↔ kwg_dualEnds P e = a := by
-- proof
  apply StatMech.FrontierD.mem_pfdEdgeBundle P a e

/--
[pfdEdgeBundle_nonempty_of_fullDualEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualBundles.lean)
-/
@[path]
private lemma pfdEdgeBundle_nonempty_of_fullDualEdge_eq
  {P : PlanarZ2Subgraph}
  {a : Sym2 (kwg_Face P)}
-- given
  (ha : a ∈ (pfdClosedDual P ⊥).edgeSet) :
-- imply
  (pfdEdgeBundle P a).Nonempty := by
-- proof
  apply StatMech.FrontierD.pfdEdgeBundle_nonempty_of_fullDualEdge P ha

/--
[pfdEffectiveParam_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualBundles.lean)
-/
@[path]
private lemma pfdEffectiveParam_pos_eq
  {P : PlanarZ2Subgraph}
  {p : Real}
  {a : Sym2 (kwg_Face P)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (ha : a ∈ (pfdClosedDual P ⊥).edgeSet) :
-- imply
  0 < pfdEffectiveParam P p a := by
-- proof
  apply StatMech.FrontierD.pfdEffectiveParam_pos P hp hp1 ha

/--
[pfdEffectiveParam_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualBundles.lean)
-/
@[path]
private lemma pfdEffectiveParam_lt_one_eq
  {P : PlanarZ2Subgraph}
  {p : Real}
  {a : Sym2 (kwg_Face P)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  pfdEffectiveParam P p a < 1 := by
-- proof
  apply StatMech.FrontierD.pfdEffectiveParam_lt_one P hp hp1 a

/--
[kwg_edge_eq_of_dualEnds_eq_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualBundles.lean)
-/
@[path]
private lemma kwg_edge_eq_of_dualEnds_eq_inner_eq
  {N m : Nat}
  {x y : FK.boxVerts 2 N}
  {e f : kwg_Edge (fkSquareBoxPlanar m)}
-- given
  (hNm : N < m)
  (hxy : (FK.boxGraph 2 N).Adj x y)
  (he : kwg_dualEnds (fkSquareBoxPlanar m) e = s(fkSquareBox_innerFaceMap N m x, fkSquareBox_innerFaceMap N m y))
  (hf : kwg_dualEnds (fkSquareBoxPlanar m) f = s(fkSquareBox_innerFaceMap N m x, fkSquareBox_innerFaceMap N m y)) :
-- imply
  e = f := by
-- proof
  apply StatMech.FrontierD.kwg_edge_eq_of_dualEnds_eq_inner hNm hxy he hf

/--
[pfdEdgeBundle_inner_card_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualBundles.lean)
-/
@[path]
private lemma pfdEdgeBundle_inner_card_eq_one_eq
  {N m : Nat}
  {a : (FK.boxGraph 2 N).edgeFinset}
-- given
  (hNm : N < m) :
-- imply
  (pfdEdgeBundle (fkSquareBoxPlanar m) (ocd_innerEdge (fkSquareBox_innerFaceMap N m) a.1)).card = 1 := by
-- proof
  apply StatMech.FrontierD.pfdEdgeBundle_inner_card_eq_one hNm a

/--
[pfdEffectiveParam_innerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualBundles.lean)
-/
@[path]
private lemma pfdEffectiveParam_innerEdge_eq
  {N m : Nat}
  {p : Real}
  {a : (FK.boxGraph 2 N).edgeFinset}
-- given
  (hNm : N < m) :
-- imply
  pfdEffectiveParam (fkSquareBoxPlanar m) p (ocd_innerEdge (fkSquareBox_innerFaceMap N m) a.1) = p := by
-- proof
  apply StatMech.FrontierD.pfdEffectiveParam_innerEdge hNm p a


-- created on 2026-10-23
