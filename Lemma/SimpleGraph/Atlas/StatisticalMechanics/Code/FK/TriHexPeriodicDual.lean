import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularStep_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma triangularStep_injective_eq :
-- imply
  Function.Injective triangularStep := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStep_injective

/--
[triangularStep_add_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma triangularStep_add_ne_zero_eq
  {i j : Fin 3} :
-- imply
  triangularStep i + triangularStep j ≠ 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStep_add_ne_zero i j

/--
[triangularIndexedEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma triangularIndexedEdge_mem_eq
  {a : TriHexEdgeIndex} :
-- imply
  triangularIndexedEdge a ∈ triangularGraph.edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularIndexedEdge_mem a

/--
[triangularEdgeChart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma triangularEdgeChart_injective_eq :
-- imply
  Function.Injective triangularEdgeChart := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularEdgeChart_injective

/--
[triangularEdgeChart_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma triangularEdgeChart_surjective_eq :
-- imply
  Function.Surjective triangularEdgeChart := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularEdgeChart_surjective

/--
[hexagonalStep_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma hexagonalStep_injective_eq :
-- imply
  Function.Injective hexagonalStep := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalStep_injective

/--
[hexagonalIndexedEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma hexagonalIndexedEdge_mem_eq
  {a : TriHexEdgeIndex} :
-- imply
  hexagonalIndexedEdge a ∈ hexagonalGraph.edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalIndexedEdge_mem a

/--
[hexagonalEdgeChart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma hexagonalEdgeChart_injective_eq :
-- imply
  Function.Injective hexagonalEdgeChart := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalEdgeChart_injective

/--
[hexagonalEdgeChart_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma hexagonalEdgeChart_surjective_eq :
-- imply
  Function.Surjective hexagonalEdgeChart := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalEdgeChart_surjective

/--
[incidentHexFaces_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma incidentHexFaces_adj_eq
  {a : TriHexEdgeIndex} :
-- imply
  hexagonalGraph.Adj (incidentHexFaces a).1 (incidentHexFaces a).2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.incidentHexFaces_adj a

/--
[triangular_edge_incident_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma triangular_edge_incident_faces_eq
  {a : TriHexEdgeIndex} :
-- imply
  let x := a.1 let y := a.1 + triangularStep a.2 x ∈ triangularFace (incidentHexFaces a).1 ∧ y ∈ triangularFace (incidentHexFaces a).1 ∧ x ∈ triangularFace (incidentHexFaces a).2 ∧ y ∈ triangularFace (incidentHexFaces a).2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_edge_incident_faces a

/--
[triHexDualEdgeEquiv_chart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean)
-/
@[path]
private lemma triHexDualEdgeEquiv_chart_eq
  {a : TriHexEdgeIndex} :
-- imply
  (triHexDualEdgeEquiv (triangularEdgeChart a) : Sym2 HexVertex) = hexagonalIndexedEdge (triHexIndexEquiv a) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexDualEdgeEquiv_chart a


-- created on 2026-10-23
