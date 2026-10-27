import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit
open StatMech StatMech.Universality


/--
[hexCSOutsideBoundary_neighbor_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExit.lean)
-/
@[path]
private lemma hexCSOutsideBoundary_neighbor_not_mem_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
  {f : Fin 3}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hf : f ≠ e.edge) :
-- imply
  hexAWNeighbor (hexAWNeighbor e.vtx.1 e.edge) f ∉ hexCSVertexSet T L := by
-- proof
  apply StatMech.Universality.hexCSOutsideBoundary_neighbor_not_mem e he f hf

/--
[hexCSOutsideBoundary_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExit.lean)
-/
@[path]
private lemma hexCSOutsideBoundary_not_mem_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  hexAWNeighbor e.vtx.1 e.edge ∉ hexCSVertexSet T L := by
-- proof
  apply StatMech.Universality.hexCSOutsideBoundary_not_mem e he

/--
[hexCSOutsideBoundary_mid_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExit.lean)
-/
@[path]
private lemma hexCSOutsideBoundary_mid_mem_iff_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
  {f : Fin 3}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  hexAWMid (hexAWNeighbor e.vtx.1 e.edge) f ∈ hexCSMids T L ↔ f = e.edge := by
-- proof
  apply StatMech.Universality.hexCSOutsideBoundary_mid_mem_iff e he f

/--
[hexCSBoundaryIncidence_eq_start_of_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExit.lean)
-/
@[path]
private lemma hexCSBoundaryIncidence_eq_start_of_mid_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (hmid : hexAWMid e.vtx.1 e.edge = hexAWStart) :
-- imply
  e = hexCSStartIncidence T L hT := by
-- proof
  apply StatMech.Universality.hexCSBoundaryIncidence_eq_start_of_mid e hmid

/--
[hexCSCanonicalHeading_halfStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExit.lean)
-/
@[path]
private lemma hexCSCanonicalHeading_halfStep_eq
  {T L : ℕ}
  {e : HexCSIncidence T L} :
-- imply
  halfStep (hexCSCanonicalHeading e) = halfStep (hexAWHeading e.vtx.1 e.edge) := by
-- proof
  apply StatMech.Universality.hexCSCanonicalHeading_halfStep e

/--
[hexCS_endpoint_boundary_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExit.lean)
-/
@[path]
private lemma hexCS_endpoint_boundary_exit_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWMid e.vtx.1 e.edge + halfStep (hexCSCanonicalHeading e) := by
-- proof
  apply StatMech.Universality.hexCS_endpoint_boundary_exit e ts he hne hadm

/--
[hexCS_boundaryExitLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExit.lean)
-/
@[path]
private lemma hexCS_boundaryExitLaw_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  HexCSBoundaryExitLaw T L hT := by
-- proof
  apply StatMech.Universality.hexCS_boundaryExitLaw T L hT


-- created on 2026-10-23
