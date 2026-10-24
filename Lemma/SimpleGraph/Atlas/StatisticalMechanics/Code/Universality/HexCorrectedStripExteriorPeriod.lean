import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod
open StatMech StatMech.Universality


/--
[hexCSHeadingFin_eq_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSHeadingFin_eq_of_dvd_eq
  {h k : ℤ}
-- given
  (hdvd : (6 : ℤ) ∣ h - k) :
-- imply
  hexCSHeadingFin h = hexCSHeadingFin k := by
-- proof
  apply StatMech.Universality.hexCSHeadingFin_eq_of_dvd hdvd

/--
[hexCS_finalHeading_eq_canonical_of_tail_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCS_finalHeading_eq_canonical_of_tail_turn_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hperiod : ons_openTurnSum (hexCSBrickDirections 1 ts) + hexCSExteriorTailTurn e = 0) :
-- imply
  hexInfra_headAccum 1 ts = hexCSCanonicalHeading e := by
-- proof
  apply StatMech.Universality.hexCS_finalHeading_eq_canonical_of_tail_turn e ts he hne hadm hperiod

/--
[hexCSBrickRadius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBrickRadius_pos_eq
  {T L : ℕ} :
-- imply
  0 < hexCSBrickRadius T L := by
-- proof
  apply StatMech.Universality.hexCSBrickRadius_pos T L

/--
[hexCS_outsideRel_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCS_outsideRel_bounds_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  -(hexCSBrickRadius T L : ℤ) < (hexCSOutsideRel e).1 ∧ (hexCSOutsideRel e).1 < (hexCSBrickRadius T L : ℤ) ∧ -(hexCSBrickRadius T L : ℤ) < (hexCSOutsideRel e).2 ∧ (hexCSOutsideRel e).2 < (hexCSBrickRadius T L : ℤ) := by
-- proof
  apply StatMech.Universality.hexCS_outsideRel_bounds e he

/--
[hexCS_left_outsideRel_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCS_left_outsideRel_sign_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hc : e.vtx.1.color = .black)
  (hedge : e.edge = 0) :
-- imply
  (0 ≤ hexAWTrans e.vtx.1 → 0 < (hexCSOutsideRel e).2) ∧ (¬ 0 ≤ hexAWTrans e.vtx.1 → (hexCSOutsideRel e).2 < 0) := by
-- proof
  apply StatMech.Universality.hexCS_left_outsideRel_sign e he hne hc hedge

/--
[hexCS_slant_outsideRel_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCS_slant_outsideRel_sign_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  (e.vtx.1.color = .white ∧ e.edge = 1 → 0 < (hexCSOutsideRel e).2) ∧ (e.vtx.1.color = .white ∧ e.edge = 2 → (hexCSOutsideRel e).2 < 0) := by
-- proof
  apply StatMech.Universality.hexCS_slant_outsideRel_sign e he

/--
[hexCS_right_zero_height_x_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCS_right_zero_height_x_neg_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hc : e.vtx.1.color = .white)
  (hedge : e.edge = 0)
  (hy : (hexCSOutsideRel e).2 = 0) :
-- imply
  (hexCSOutsideRel e).1 < 0 := by
-- proof
  apply StatMech.Universality.hexCS_right_zero_height_x_neg e he hc hedge hy

/--
[hexCS_right_tail_first_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCS_right_tail_first_pos_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hc : e.vtx.1.color = .white)
  (hedge : e.edge = 0) :
-- imply
  0 < (hexCSOutsideRel e).1 + (hexCSBrickRadius T L : ℤ) := by
-- proof
  apply StatMech.Universality.hexCS_right_tail_first_pos e he hc hedge

/--
[hexCSBoundarySource_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundarySource_ne_nil_eq
  {T L R : ℕ}
  {e : HexCSIncidence T L}
-- given
  (hR : 0 < R)
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  hexCSBoundarySource R e ≠ [] := by
-- proof
  apply StatMech.Universality.hexCSBoundarySource_ne_nil e hR he

/--
[hexCSBoundarySource_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundarySource_head_eq
  {T L R : ℕ}
  {e : HexCSIncidence T L}
-- given
  (hR : 0 < R)
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  (hexCSBoundarySource R e).head! = 0 := by
-- proof
  apply StatMech.Universality.hexCSBoundarySource_head e hR he

/--
[hexCSBoundarySource_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundarySource_getLast_eq
  {T L R : ℕ}
  {e : HexCSIncidence T L}
-- given
  (hR : 0 < R)
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  (hexCSBoundarySource R e).getLast! = 2 := by
-- proof
  apply StatMech.Universality.hexCSBoundarySource_getLast e hR he

/--
[hexCSBoundaryTail_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundaryTail_ne_nil_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  hexCSBoundaryTail (hexCSBrickRadius T L) e ≠ [] := by
-- proof
  apply StatMech.Universality.hexCSBoundaryTail_ne_nil e he

/--
[hexCSBoundaryTail_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundaryTail_head_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  (hexCSBoundaryTail (hexCSBrickRadius T L) e).head! = hexBrickDir (hexCSHeadingFin (hexCSCanonicalHeading e)) := by
-- proof
  apply StatMech.Universality.hexCSBoundaryTail_head e he

/--
[hexCSBoundaryTail_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundaryTail_getLast_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  (hexCSBoundaryTail (hexCSBrickRadius T L) e).getLast! = 0 := by
-- proof
  apply StatMech.Universality.hexCSBoundaryTail_getLast e he

/--
[hexCSBoundary_exterior_openTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundary_exterior_openTurn_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  ons_openTurnSum (hexCSBoundarySource (hexCSBrickRadius T L) e) + ons_openTurnSum (hexCSBoundaryTail (hexCSBrickRadius T L) e) = hexCSExteriorTailTurn e := by
-- proof
  apply StatMech.Universality.hexCSBoundary_exterior_openTurn e he

/--
[hexCSBoundaryPeriod_displacement_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundaryPeriod_displacement_fst_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  (ons_pathDisplacement (hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts)).1 = 2 * (hexCSBrickRadius T L : ℤ) + 1 := by
-- proof
  apply StatMech.Universality.hexCSBoundaryPeriod_displacement_fst e ts he hne hadm

/--
[hexCSSourceBelow_mem_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSSourceBelow_mem_cases_eq
  {R : ℕ}
  {z : ℤ × ℤ}
-- given
  (hz : z ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast) :
-- imply
  (∃ k : ℕ, k < 2 * R ∧ z = ((k : ℤ), 0)) ∨ (∃ k : ℕ, k < R ∧ z = (((2 * R : ℕ) : ℤ), (k : ℤ))) ∨ (∃ k : ℕ, k < R ∧ z = ((2 * R : ℕ) - (k : ℤ), (R : ℤ))) := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_mem_cases R z hz

/--
[hexCSSourceAbove_mem_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSSourceAbove_mem_cases_eq
  {R : ℕ}
  {z : ℤ × ℤ}
-- given
  (hz : z ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast) :
-- imply
  (∃ k : ℕ, k < 2 * R ∧ z = ((k : ℤ), 0)) ∨ (∃ k : ℕ, k < R ∧ z = (((2 * R : ℕ) : ℤ), -(k : ℤ))) ∨ (∃ k : ℕ, k < R ∧ z = ((2 * R : ℕ) - (k : ℤ), -(R : ℤ))) := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_mem_cases R z hz

/--
[hexCSEastTail_mem_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSEastTail_mem_cases_eq
  {R : ℕ}
  {dx : ℤ}
  {z : ℤ × ℤ}
-- given
  (hz : z ∈ (ons_pathVertices (hexCSEastTail R dx)).dropLast) :
-- imply
  ∃ k : ℕ, k < ((R : ℤ) + 1 - dx).toNat ∧ z = ((k : ℤ), 0) := by
-- proof
  apply StatMech.Universality.hexCSEastTail_mem_cases R dx z hz

/--
[hexCSWestNorthEastTail_mem_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSWestNorthEastTail_mem_cases_eq
  {R : ℕ}
  {dx dy : ℤ}
  {z : ℤ × ℤ}
-- given
  (hW : 0 < dx + R)
  (hN : 0 < (R : ℤ) - dy)
  (hz : z ∈ (ons_pathVertices (hexCSWestNorthEastTail R dx dy)).dropLast) :
-- imply
  (∃ k : ℕ, k < (dx + R).toNat ∧ z = (-(k : ℤ), 0)) ∨ (∃ k : ℕ, k < ((R : ℤ) - dy).toNat ∧ z = (-(dx + R), (k : ℤ))) ∨ (∃ k : ℕ, k < 2 * R + 1 ∧ z = (-(dx + R) + (k : ℤ), (R : ℤ) - dy)) := by
-- proof
  apply StatMech.Universality.hexCSWestNorthEastTail_mem_cases R dx dy hW hN z hz

/--
[hexCSSouthEastTail_mem_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSSouthEastTail_mem_cases_eq
  {R : ℕ}
  {dx dy : ℤ}
  {z : ℤ × ℤ}
-- given
  (hS : 0 < dy + R)
  (hz : z ∈ (ons_pathVertices (hexCSSouthEastTail R dx dy)).dropLast) :
-- imply
  (∃ k : ℕ, k < (dy + R).toNat ∧ z = (0, -(k : ℤ))) ∨ (∃ k : ℕ, k < ((R : ℤ) + 1 - dx).toNat ∧ z = ((k : ℤ), -(dy + R))) := by
-- proof
  apply StatMech.Universality.hexCSSouthEastTail_mem_cases R dx dy hS z hz

/--
[hexCSSourceBelow_trace_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSSourceBelow_trace_disjoint_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  ∀ p ∈ (ons_pathVertices (hexCSSourceBelow (hexCSBrickRadius T L))).dropLast, ∀ c ∈ (ons_pathVertices (hexCSBrickDirections 1 ts)).dropLast, p ≠ ons_pathDisplacement (hexCSSourceBelow (hexCSBrickRadius T L)) + c := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_trace_disjoint e ts he hne hadm

/--
[hexCSSourceAbove_trace_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSSourceAbove_trace_disjoint_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  ∀ p ∈ (ons_pathVertices (hexCSSourceAbove (hexCSBrickRadius T L))).dropLast, ∀ c ∈ (ons_pathVertices (hexCSBrickDirections 1 ts)).dropLast, p ≠ ons_pathDisplacement (hexCSSourceAbove (hexCSBrickRadius T L)) + c := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_trace_disjoint e ts he hne hadm

/--
[hexCS_trace_tail_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCS_trace_tail_disjoint_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  ∀ c ∈ (ons_pathVertices (hexCSBrickDirections 1 ts)).dropLast, ∀ s ∈ (ons_pathVertices (hexCSBoundaryTail (hexCSBrickRadius T L) e)).dropLast, c ≠ ons_pathDisplacement (hexCSBrickDirections 1 ts) + s := by
-- proof
  apply StatMech.Universality.hexCS_trace_tail_disjoint e ts he hne hadm

/--
[hexCS_source_tail_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCS_source_tail_disjoint_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  ∀ p ∈ (ons_pathVertices (hexCSBoundarySource (hexCSBrickRadius T L) e)).dropLast, ∀ s ∈ (ons_pathVertices (hexCSBoundaryTail (hexCSBrickRadius T L) e)).dropLast, p ≠ ons_pathDisplacement (hexCSBoundarySource (hexCSBrickRadius T L) e) + ons_pathDisplacement (hexCSBrickDirections 1 ts) + s := by
-- proof
  apply StatMech.Universality.hexCS_source_tail_disjoint e ts he hne hadm

/--
[hexCSBoundarySource_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundarySource_vertices_dropLast_nodup_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  (ons_pathVertices (hexCSBoundarySource (hexCSBrickRadius T L) e)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSBoundarySource_vertices_dropLast_nodup e he

/--
[hexCSBoundaryTail_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundaryTail_vertices_dropLast_nodup_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  (ons_pathVertices (hexCSBoundaryTail (hexCSBrickRadius T L) e)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSBoundaryTail_vertices_dropLast_nodup e he

/--
[hexCSBoundaryPeriod_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundaryPeriod_vertices_dropLast_nodup_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  (ons_pathVertices (hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSBoundaryPeriod_vertices_dropLast_nodup e ts he hne hadm

/--
[hexCSBoundarySource_displacement_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundarySource_displacement_fst_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  (ons_pathDisplacement (hexCSBoundarySource (hexCSBrickRadius T L) e)).1 = (hexCSBrickRadius T L : ℤ) := by
-- proof
  apply StatMech.Universality.hexCSBoundarySource_displacement_fst e he

/--
[hexCSBoundaryPeriod_fst_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundaryPeriod_fst_slab_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  ∀ z ∈ (ons_pathVertices (hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts)).dropLast, 0 ≤ z.1 ∧ z.1 < 2 * (hexCSBrickRadius T L : ℤ) + 1 := by
-- proof
  apply StatMech.Universality.hexCSBoundaryPeriod_fst_slab e ts he hne hadm

/--
[hexCSBoundaryPeriod_cyclicTurnSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundaryPeriod_cyclicTurnSum_eq_zero_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  ons_cyclicTurnSum (hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts) = 0 := by
-- proof
  apply StatMech.Universality.hexCSBoundaryPeriod_cyclicTurnSum_eq_zero e ts he hne hadm

/--
[hexCSBoundaryPeriod_cyclicTurnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundaryPeriod_cyclicTurnSum_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  ons_cyclicTurnSum (hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts) = ons_openTurnSum (hexCSBrickDirections 1 ts) + hexCSExteriorTailTurn e := by
-- proof
  apply StatMech.Universality.hexCSBoundaryPeriod_cyclicTurnSum e ts he hne hadm

/--
[hexCSBrick_openTurn_add_exterior_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBrick_openTurn_add_exterior_eq_zero_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  ons_openTurnSum (hexCSBrickDirections 1 ts) + hexCSExteriorTailTurn e = 0 := by
-- proof
  apply StatMech.Universality.hexCSBrick_openTurn_add_exterior_eq_zero e ts he hne hadm

/--
[hexCS_finalHeading_eq_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCS_finalHeading_eq_canonical_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  hexInfra_headAccum 1 ts = hexCSCanonicalHeading e := by
-- proof
  apply StatMech.Universality.hexCS_finalHeading_eq_canonical e ts he hne hadm

/--
[hexCSBoundaryWindowLaw_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSBoundaryWindowLaw_unconditional_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  HexCSBoundaryWindowLaw T L hT := by
-- proof
  apply StatMech.Universality.hexCSBoundaryWindowLaw_unconditional T L hT

/--
[hexCSCanonicalWindingLaw_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean)
-/
@[path]
private lemma hexCSCanonicalWindingLaw_unconditional_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  HexCSCanonicalWindingLaw T L hT := by
-- proof
  apply StatMech.Universality.hexCSCanonicalWindingLaw_unconditional T L hT


-- created on 2026-10-23
