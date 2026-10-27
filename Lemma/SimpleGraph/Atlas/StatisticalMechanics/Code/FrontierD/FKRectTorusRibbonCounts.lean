import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonCounts.Part2
open StatMech StatMech.FrontierD


/--
[fkRectTorus_card_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRibbonCounts.lean)
-/
@[path]
private lemma fkRectTorus_card_vertex_eq
  {R : FKRectTorus} :
-- imply
  Fintype.card R.Vertex = R.width * R.height := by
-- proof
  apply StatMech.FrontierD.fkRectTorus_card_vertex R

/--
[fkRectTorus_card_edgeIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRibbonCounts.lean)
-/
@[path]
private lemma fkRectTorus_card_edgeIndex_eq
  {R : FKRectTorus} :
-- imply
  Fintype.card R.EdgeIndex = 2 * R.width * R.height := by
-- proof
  apply StatMech.FrontierD.fkRectTorus_card_edgeIndex R

/--
[fkRectTorus_cellularEuler_genus_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRibbonCounts.lean)
-/
@[path]
private lemma fkRectTorus_cellularEuler_genus_one_eq
  {R : FKRectTorus} :
-- imply
  Fintype.card R.Vertex + fkRectTorusCellularFaceCount R + 2 * 1 = Fintype.card R.EdgeIndex + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectTorus_cellularEuler_genus_one R

/--
[fkRectTorus_vertex_eq_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRibbonCounts.lean)
-/
@[path]
private lemma fkRectTorus_vertex_eq_faceCount_eq
  {R : FKRectTorus} :
-- imply
  Fintype.card R.Vertex = fkRectTorusCellularFaceCount R := by
-- proof
  apply StatMech.FrontierD.fkRectTorus_vertex_eq_faceCount R


-- created on 2026-10-23
