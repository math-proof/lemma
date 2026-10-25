import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
open SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularIndexedEdge_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean)
-/
@[path]
private lemma triangularIndexedEdge_add_eq
  {z : Site 2}
  {a : TriHexEdgeIndex} :
-- imply
  triangularIndexedEdge (a.1 + z, a.2) = Sym2.map (siteTranslate z) (triangularIndexedEdge a) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularIndexedEdge_add z a

/--
[hexagonalIndexedEdge_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean)
-/
@[path]
private lemma hexagonalIndexedEdge_add_eq
  {z : Site 2}
  {a : TriHexEdgeIndex} :
-- imply
  hexagonalIndexedEdge (a.1 + z, a.2) = Sym2.map (hexTranslate z) (hexagonalIndexedEdge a) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalIndexedEdge_add z a

/--
[triHexIndexEquiv_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean)
-/
@[path]
private lemma triHexIndexEquiv_add_eq
  {z : Site 2}
  {a : TriHexEdgeIndex} :
-- imply
  triHexIndexEquiv (a.1 + z, a.2) = ((triHexIndexEquiv a).1 + z, (triHexIndexEquiv a).2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexIndexEquiv_add z a

/--
[triHexDualEdgeEquiv_add_chart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean)
-/
@[path]
private lemma triHexDualEdgeEquiv_add_chart_eq
  {z : Site 2}
  {a : TriHexEdgeIndex} :
-- imply
  ((triHexDualEdgeEquiv (triangularEdgeChart (a.1 + z, a.2)) : hexagonalGraph.edgeSet) : Sym2 HexVertex) = Sym2.map (hexTranslate z) ((triHexDualEdgeEquiv (triangularEdgeChart a) : hexagonalGraph.edgeSet) : Sym2 HexVertex) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexDualEdgeEquiv_add_chart z a

/--
[triangularEdgeTranslate_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean)
-/
@[path]
private lemma triangularEdgeTranslate_val_eq
  {z : Site 2}
  {e : triangularGraph.edgeSet} :
-- imply
  ((triangularEdgeTranslate z e : triangularGraph.edgeSet) : Sym2 (Site 2)) = Sym2.map (siteTranslate z) (e : Sym2 (Site 2)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularEdgeTranslate_val z e

/--
[hexagonalEdgeTranslate_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean)
-/
@[path]
private lemma hexagonalEdgeTranslate_val_eq
  {z : Site 2}
  {e : hexagonalGraph.edgeSet} :
-- imply
  ((hexagonalEdgeTranslate z e : hexagonalGraph.edgeSet) : Sym2 HexVertex) = Sym2.map (hexTranslate z) (e : Sym2 HexVertex) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalEdgeTranslate_val z e

/--
[triHexDualEdgeEquiv_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean)
-/
@[path]
private lemma triHexDualEdgeEquiv_add_eq
  {z : Site 2}
  {e : triangularGraph.edgeSet} :
-- imply
  triHexDualEdgeEquiv (triangularEdgeTranslate z e) = hexagonalEdgeTranslate z (triHexDualEdgeEquiv e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexDualEdgeEquiv_add z e


-- created on 2026-10-23
