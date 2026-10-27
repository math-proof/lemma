import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
open StatMech StatMech.Universality


/--
[hexCSInStrip_mem_coordBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSInStrip_mem_coordBox_eq
  {T L : ℕ}
  {c : HexAWCoord}
-- given
  (hc : hexCSInStrip T L c) :
-- imply
  c ∈ hexAWCoordBox T L := by
-- proof
  apply StatMech.Universality.hexCSInStrip_mem_coordBox T L c hc

/--
[hexCS_mem_vertexSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCS_mem_vertexSet_iff_eq
  {T L : ℕ}
  {c : HexAWCoord} :
-- imply
  c ∈ hexCSVertexSet T L ↔ hexCSInStrip T L c := by
-- proof
  apply StatMech.Universality.hexCS_mem_vertexSet_iff T L c

/--
[hexCSOrigin_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSOrigin_mem_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexAWOriginCoord ∈ hexCSVertexSet T L := by
-- proof
  apply StatMech.Universality.hexCSOrigin_mem T L hT

/--
[hexCSInStrip_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSInStrip_reflect_iff_eq
  {T L : ℕ}
  {c : HexAWCoord} :
-- imply
  hexCSInStrip T L (hexAWReflectCoord c) ↔ hexCSInStrip T L c := by
-- proof
  apply StatMech.Universality.hexCSInStrip_reflect_iff T L c

/--
[hexCSVertexSet_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSVertexSet_reflect_iff_eq
  {T L : ℕ}
  {c : HexAWCoord} :
-- imply
  hexAWReflectCoord c ∈ hexCSVertexSet T L ↔ c ∈ hexCSVertexSet T L := by
-- proof
  apply StatMech.Universality.hexCSVertexSet_reflect_iff T L c

/--
[hexCSReflectVertex_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSReflectVertex_invol_eq
  {T L : ℕ}
  {v : HexCSVertex T L} :
-- imply
  hexCSReflectVertex (hexCSReflectVertex v) = v := by
-- proof
  apply StatMech.Universality.hexCSReflectVertex_invol v

/--
[hexCS_mem_incidences](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCS_mem_incidences_eq
  {T L : ℕ}
  {e : HexCSIncidence T L} :
-- imply
  e ∈ hexCSIncidences T L := by
-- proof
  apply StatMech.Universality.hexCS_mem_incidences e

/--
[hexCS_mem_interior_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCS_mem_interior_iff_eq
  {T L : ℕ}
  {e : HexCSIncidence T L} :
-- imply
  e ∈ hexCSInteriorIncidences T L ↔ hexCSIsInterior e := by
-- proof
  apply StatMech.Universality.hexCS_mem_interior_iff e

/--
[hexCS_mem_boundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCS_mem_boundary_iff_eq
  {T L : ℕ}
  {e : HexCSIncidence T L} :
-- imply
  e ∈ hexCSBoundaryIncidences T L ↔ ¬ hexCSIsInterior e := by
-- proof
  apply StatMech.Universality.hexCS_mem_boundary_iff e

/--
[hexCSReflectIncidence_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSReflectIncidence_invol_eq
  {T L : ℕ}
  {e : HexCSIncidence T L} :
-- imply
  hexCSReflectIncidence (hexCSReflectIncidence e) = e := by
-- proof
  apply StatMech.Universality.hexCSReflectIncidence_invol e

/--
[hexCSIsInterior_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSIsInterior_reflect_iff_eq
  {T L : ℕ}
  {e : HexCSIncidence T L} :
-- imply
  hexCSIsInterior (hexCSReflectIncidence e) ↔ hexCSIsInterior e := by
-- proof
  apply StatMech.Universality.hexCSIsInterior_reflect_iff e

/--
[hexCSReflectIncidence_mem_boundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSReflectIncidence_mem_boundary_iff_eq
  {T L : ℕ}
  {e : HexCSIncidence T L} :
-- imply
  hexCSReflectIncidence e ∈ hexCSBoundaryIncidences T L ↔ e ∈ hexCSBoundaryIncidences T L := by
-- proof
  apply StatMech.Universality.hexCSReflectIncidence_mem_boundary_iff e

/--
[hexCS_boundary_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCS_boundary_classification_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  (e.vtx.1.color = .black ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = 0) ∨ (e.vtx.1.color = .white ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = T) ∨ (e.vtx.1.color = .white ∧ e.edge = 1 ∧ e.vtx.1.i = L) ∨ (e.vtx.1.color = .white ∧ e.edge = 2 ∧ e.vtx.1.j = L) := by
-- proof
  apply StatMech.Universality.hexCS_boundary_classification e he

/--
[hexCS_mem_boundary_of_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCS_mem_boundary_of_classification_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (he : (e.vtx.1.color = .black ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = 0) ∨ (e.vtx.1.color = .white ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = T) ∨ (e.vtx.1.color = .white ∧ e.edge = 1 ∧ e.vtx.1.i = L) ∨ (e.vtx.1.color = .white ∧ e.edge = 2 ∧ e.vtx.1.j = L)) :
-- imply
  e ∈ hexCSBoundaryIncidences T L := by
-- proof
  apply StatMech.Universality.hexCS_mem_boundary_of_classification e he

/--
[hexCS_boundary_heading_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCS_boundary_heading_cases_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  hexAWHeading e.vtx.1 e.edge = 4 ∨ hexAWHeading e.vtx.1 e.edge = 7 ∨ hexAWHeading e.vtx.1 e.edge = 3 ∨ hexAWHeading e.vtx.1 e.edge = 5 := by
-- proof
  apply StatMech.Universality.hexCS_boundary_heading_cases e he

/--
[hexCSStartIncidence_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSStartIncidence_mid_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexAWMid (hexCSStartIncidence T L hT).vtx.1 (hexCSStartIncidence T L hT).edge = hexAWStart := by
-- proof
  apply StatMech.Universality.hexCSStartIncidence_mid T L hT

/--
[hexCSStartIncidence_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSStartIncidence_mem_boundary_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSStartIncidence T L hT ∈ hexCSBoundaryIncidences T L := by
-- proof
  apply StatMech.Universality.hexCSStartIncidence_mem_boundary T L hT

/--
[hexCSCanonicalHeading_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSCanonicalHeading_unit_eq
  {T L : ℕ}
  {e : HexCSIncidence T L} :
-- imply
  hexUnit (hexCSCanonicalHeading e) = hexUnit (hexAWHeading e.vtx.1 e.edge) := by
-- proof
  apply StatMech.Universality.hexCSCanonicalHeading_unit e

/--
[hexCSCanonicalHeading_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCSCanonicalHeading_reflect_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT) :
-- imply
  hexCSCanonicalHeading (hexCSReflectIncidence e) = 2 - hexCSCanonicalHeading e := by
-- proof
  apply StatMech.Universality.hexCSCanonicalHeading_reflect e he hne

/--
[hexCS_boundary_cosine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCS_boundary_cosine_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  Real.cos (hexPhase_sideTilt (hexCSCanonicalHeading e) + (5 / 8 : ℝ) * hexCSCanonicalWinding e) = match hexCSBoundaryClass e with := by
-- proof
  apply StatMech.Universality.hexCS_boundary_cosine e he

/--
[hexCS_deterministic_winding_of_unrestricted_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean)
-/
@[path]
private lemma hexCS_deterministic_winding_of_unrestricted_law_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (hlaw : HexCSUnrestrictedCanonicalWindingLaw T L hT)
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  (ofTurns hexAWStart 1 ts).turning = hexCSCanonicalWinding e := by
-- proof
  apply StatMech.Universality.hexCS_deterministic_winding_of_unrestricted_law hlaw e he hne ts hlegal hend


-- created on 2026-10-23
