import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part17
open SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[siteLexNonnegative_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma siteLexNonnegative_zero_eq :
-- imply
  siteLexNonnegative (0 : Site 2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteLexNonnegative_zero

/--
[siteLexNonnegative_neg_of_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma siteLexNonnegative_neg_of_not_eq
  {d : Site 2}
-- given
  (h : ¬ siteLexNonnegative d) :
-- imply
  siteLexNonnegative (-d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteLexNonnegative_neg_of_not h

/--
[not_siteLexNonnegative_neg_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma not_siteLexNonnegative_neg_of_ne_zero_eq
  {d : Site 2}
-- given
  (hd : d ≠ 0)
  (h : siteLexNonnegative d) :
-- imply
  ¬ siteLexNonnegative (-d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.not_siteLexNonnegative_neg_of_ne_zero hd h

/--
[triangularPairNormal_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triangularPairNormal_symm_eq
  {x y : Site 2} :
-- imply
  triangularPairNormal x y = triangularPairNormal y x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPairNormal_symm x y

/--
[triangularPairOrbitTo_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triangularPairOrbitTo_mk_eq
  {x y : Site 2} :
-- imply
  triangularPairOrbitTo s(x, y) = triangularPairNormal x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPairOrbitTo_mk x y

/--
[triangularPairOrbitFrom_to](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triangularPairOrbitFrom_to_eq
  {e : Sym2 (Site 2)} :
-- imply
  triangularPairOrbitFrom (triangularPairOrbitTo e) = e := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPairOrbitFrom_to e

/--
[triangularPairOrbitTo_from](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triangularPairOrbitTo_from_eq
  {a : Site 2 × TriangularPairShape} :
-- imply
  triangularPairOrbitTo (triangularPairOrbitFrom a) = a := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPairOrbitTo_from a

/--
[triangularPairNormal_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triangularPairNormal_add_eq
  {z x y : Site 2} :
-- imply
  triangularPairNormal (x + z) (y + z) = (triangularPairNormal x y).map (fun b => b + z) id := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPairNormal_add z x y

/--
[triangularPairOrbitEquiv_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triangularPairOrbitEquiv_add_eq
  {z : Site 2}
  {e : Sym2 (Site 2)} :
-- imply
  triangularPairOrbitEquiv (Sym2.map (siteTranslate z) e) = (triangularPairOrbitEquiv e).map (fun b => b + z) id := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPairOrbitEquiv_add z e

/--
[not_siteLexPositive_neg_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma not_siteLexPositive_neg_of_pos_eq
  {d : Site 2}
-- given
  (h : siteLexPositive d) :
-- imply
  ¬ siteLexPositive (-d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.not_siteLexPositive_neg_of_pos h

/--
[site_eq_zero_of_not_lexPositive_or_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma site_eq_zero_of_not_lexPositive_or_neg_eq
  {d : Site 2}
-- given
  (h : ¬ siteLexPositive d)
  (hn : ¬ siteLexPositive (-d)) :
-- imply
  d = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.site_eq_zero_of_not_lexPositive_or_neg h hn

/--
[hexagonalPairNormal_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma hexagonalPairNormal_symm_eq
  {u v : HexVertex} :
-- imply
  hexagonalPairNormal u v = hexagonalPairNormal v u := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPairNormal_symm u v

/--
[hexagonalPairOrbitTo_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma hexagonalPairOrbitTo_mk_eq
  {u v : HexVertex} :
-- imply
  hexagonalPairOrbitTo s(u, v) = hexagonalPairNormal u v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPairOrbitTo_mk u v

/--
[hexagonalPairOrbitFrom_to](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma hexagonalPairOrbitFrom_to_eq
  {e : Sym2 HexVertex} :
-- imply
  hexagonalPairOrbitFrom (hexagonalPairOrbitTo e) = e := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPairOrbitFrom_to e

/--
[hexagonalPairOrbitTo_from](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma hexagonalPairOrbitTo_from_eq
  {a : Site 2 × HexagonalPairShape} :
-- imply
  hexagonalPairOrbitTo (hexagonalPairOrbitFrom a) = a := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPairOrbitTo_from a

/--
[hexagonalPairNormal_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma hexagonalPairNormal_add_eq
  {z : Site 2}
  {u v : HexVertex} :
-- imply
  hexagonalPairNormal (hexTranslate z u) (hexTranslate z v) = (hexagonalPairNormal u v).map (fun b => b + z) id := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPairNormal_add z u v

/--
[hexagonalPairOrbitEquiv_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma hexagonalPairOrbitEquiv_add_eq
  {z : Site 2}
  {e : Sym2 HexVertex} :
-- imply
  hexagonalPairOrbitEquiv (Sym2.map (hexTranslate z) e) = (hexagonalPairOrbitEquiv e).map (fun b => b + z) id := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPairOrbitEquiv_add z e

/--
[triangularEdgePairShape_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triangularEdgePairShape_injective_eq :
-- imply
  Function.Injective triangularEdgePairShape := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularEdgePairShape_injective

/--
[hexagonalEdgePairShape_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma hexagonalEdgePairShape_injective_eq :
-- imply
  Function.Injective hexagonalEdgePairShape := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalEdgePairShape_injective

/--
[triHexPairShapeEquiv_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triHexPairShapeEquiv_edge_eq
  {i : Fin 3} :
-- imply
  triHexPairShapeEquiv (triangularEdgePairShape i) = hexagonalEdgePairShape i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPairShapeEquiv_edge i

/--
[triHexPairShapeOffset_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triHexPairShapeOffset_edge_eq
  {i : Fin 3} :
-- imply
  triangularEdgePairBase i + triHexPairShapeOffset (triangularEdgePairShape i) = (triHexIndexEquiv (0, i)).1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPairShapeOffset_edge i

/--
[triHexPairOrbitDataEquiv_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triHexPairOrbitDataEquiv_add_eq
  {z : Site 2}
  {a : Site 2 × TriangularPairShape} :
-- imply
  triHexPairOrbitDataEquiv (a.map (fun b => b + z) id) = (triHexPairOrbitDataEquiv a).map (fun b => b + z) id := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPairOrbitDataEquiv_add z a

/--
[triHexFullDualEdgeEquiv_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triHexFullDualEdgeEquiv_shift_eq
  {z : Site 2}
  {e : Sym2 (Site 2)} :
-- imply
  triHexFullDualEdgeEquiv (Sym2.map (siteTranslate z) e) = Sym2.map (hexTranslate z) (triHexFullDualEdgeEquiv e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFullDualEdgeEquiv_shift z e

/--
[triangularPairOrbitEquiv_indexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triangularPairOrbitEquiv_indexedEdge_eq
  {a : TriHexEdgeIndex} :
-- imply
  triangularPairOrbitEquiv (triangularIndexedEdge a) = (a.1 + triangularEdgePairBase a.2, triangularEdgePairShape a.2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPairOrbitEquiv_indexedEdge a

/--
[hexagonalPairOrbitEquiv_indexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma hexagonalPairOrbitEquiv_indexedEdge_eq
  {a : TriHexEdgeIndex} :
-- imply
  hexagonalPairOrbitEquiv (hexagonalIndexedEdge a) = (a.1, hexagonalEdgePairShape a.2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPairOrbitEquiv_indexedEdge a

/--
[triHexFullDualEdgeEquiv_indexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triHexFullDualEdgeEquiv_indexedEdge_eq
  {a : TriHexEdgeIndex} :
-- imply
  triHexFullDualEdgeEquiv (triangularIndexedEdge a) = hexagonalIndexedEdge (triHexIndexEquiv a) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFullDualEdgeEquiv_indexedEdge a

/--
[triHexFullDualEdgeEquiv_edgeChart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triHexFullDualEdgeEquiv_edgeChart_eq
  {a : TriHexEdgeIndex} :
-- imply
  triHexFullDualEdgeEquiv (triangularEdgeChart a : Sym2 (Site 2)) = (triHexDualEdgeEquiv (triangularEdgeChart a) : Sym2 HexVertex) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFullDualEdgeEquiv_edgeChart a

/--
[triHexFullDualEdgeEquiv_mem_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triHexFullDualEdgeEquiv_mem_edgeSet_eq
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ triangularGraph.edgeSet ↔ triHexFullDualEdgeEquiv e ∈ hexagonalGraph.edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFullDualEdgeEquiv_mem_edgeSet e

/--
[triHexFullDualEdgeEquiv_eq_edgeDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean)
-/
@[path]
private lemma triHexFullDualEdgeEquiv_eq_edgeDual_eq
  {e : triangularGraph.edgeSet} :
-- imply
  triHexFullDualEdgeEquiv (e : Sym2 (Site 2)) = (triHexDualEdgeEquiv e : Sym2 HexVertex) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFullDualEdgeEquiv_eq_edgeDual e


-- created on 2026-10-23
