import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
open StatMech StatMech.Universality


/--
[hexCSHeadingFin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSHeadingFin_zero_eq :
-- imply
  hexCSHeadingFin 0 = 0 := by
-- proof
  apply StatMech.Universality.hexCSHeadingFin_zero

/--
[hexCSHeadingFin_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSHeadingFin_one_eq :
-- imply
  hexCSHeadingFin 1 = 1 := by
-- proof
  apply StatMech.Universality.hexCSHeadingFin_one

/--
[hexCSHeadingFin_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSHeadingFin_add_eq
-- given
  (h k : ℤ) :
-- imply
  hexCSHeadingFin (h + k) = hexCSHeadingFin h + hexCSHeadingFin k := by
-- proof
  apply StatMech.Universality.hexCSHeadingFin_add h k

/--
[hexCSHeadingFin_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSHeadingFin_dvd_eq
-- given
  (h : ℤ) :
-- imply
  (6 : ℤ) ∣ h - (hexCSHeadingFin h).val := by
-- proof
  apply StatMech.Universality.hexCSHeadingFin_dvd h

/--
[hexCSHeadingFin_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSHeadingFin_unit_eq
-- given
  (h : ℤ) :
-- imply
  hexUnit h = hexUnit (hexCSHeadingFin h).val := by
-- proof
  apply StatMech.Universality.hexCSHeadingFin_unit h

/--
[hexCSHeadingFin_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSHeadingFin_turn_eq
-- given
  (h t : ℤ)
  (ht : t = 1 ∨ t = -1) :
-- imply
  hexCSHeadingFin (h + t) = hexHeadingTurn (hexCSHeadingFin h) t := by
-- proof
  apply StatMech.Universality.hexCSHeadingFin_turn h t ht

/--
[hexCSBrickDirections_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBrickDirections_nil_eq
-- given
  (h : ℤ) :
-- imply
  hexCSBrickDirections h [] = [hexBrickDir (hexCSHeadingFin h)] := by
-- proof
  apply StatMech.Universality.hexCSBrickDirections_nil h

/--
[hexCSBrickDirections_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBrickDirections_cons_eq
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  hexCSBrickDirections h (t :: ts) = hexBrickDir (hexCSHeadingFin h) :: hexCSBrickDirections (h + t) ts := by
-- proof
  apply StatMech.Universality.hexCSBrickDirections_cons h t ts

/--
[hexCSBrickDirections_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBrickDirections_length_eq
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (hexCSBrickDirections h ts).length = ts.length + 1 := by
-- proof
  apply StatMech.Universality.hexCSBrickDirections_length h ts

/--
[hexCSBrickDirections_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBrickDirections_ne_nil_eq
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexCSBrickDirections h ts ≠ [] := by
-- proof
  apply StatMech.Universality.hexCSBrickDirections_ne_nil h ts

/--
[hexCSBrickDirections_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBrickDirections_head_eq
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (hexCSBrickDirections h ts).head! = hexBrickDir (hexCSHeadingFin h) := by
-- proof
  apply StatMech.Universality.hexCSBrickDirections_head h ts

/--
[hexCSBrickDirections_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBrickDirections_getLast_eq
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (hexCSBrickDirections h ts).getLast! = hexBrickDir (hexCSHeadingFin (hexInfra_headAccum h ts)) := by
-- proof
  apply StatMech.Universality.hexCSBrickDirections_getLast h ts

/--
[hexCS_brick_open_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_brick_open_telescope_eq
  {ts : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  2 * ts.sum + 3 * ons_openTurnSum (hexCSBrickDirections h ts) = hexBrickTurnPotential (hexCSHeadingFin (hexInfra_headAccum h ts)) - hexBrickTurnPotential (hexCSHeadingFin h) := by
-- proof
  apply StatMech.Universality.hexCS_brick_open_telescope h ts hlegal

/--
[hexCSHeadingFits_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSHeadingFits_start_eq :
-- imply
  HexCSHeadingFits hexCSOutsideStartCoord (hexCSHeadingFin 1) := by
-- proof
  apply StatMech.Universality.hexCSHeadingFits_start

/--
[hexCSEdgeOfHeading_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEdgeOfHeading_mod_eq
  {c : HexAWCoord}
-- given
  (h : Fin 6)
  (hfit : HexCSHeadingFits c h) :
-- imply
  hexAWHeadingMod c (hexCSEdgeOfHeading c h) = h := by
-- proof
  apply StatMech.Universality.hexCSEdgeOfHeading_mod c h hfit

/--
[hexAWHeadingMod_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexAWHeadingMod_unit_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexUnit (hexAWHeading c e) = hexUnit (hexAWHeadingMod c e).val := by
-- proof
  apply StatMech.Universality.hexAWHeadingMod_unit c e

/--
[hexCSEdgeOfHeading_halfStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEdgeOfHeading_halfStep_eq
  {c : HexAWCoord}
-- given
  (h0 : ℤ)
  (hfit : HexCSHeadingFits c (hexCSHeadingFin h0)) :
-- imply
  halfStep h0 = halfStep (hexAWHeading c (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) := by
-- proof
  apply StatMech.Universality.hexCSEdgeOfHeading_halfStep c h0 hfit

/--
[hexCSHeadingFits_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSHeadingFits_step_eq
  {c : HexAWCoord}
  {t : ℤ}
-- given
  (h : Fin 6)
  (hfit : HexCSHeadingFits c h)
  (ht : t = 1 ∨ t = -1) :
-- imply
  HexCSHeadingFits (hexAWNeighbor c (hexCSEdgeOfHeading c h)) (hexHeadingTurn h t) := by
-- proof
  apply StatMech.Universality.hexCSHeadingFits_step c h t hfit ht

/--
[hexCSCoordPath_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSCoordPath_length_eq
  {c : HexAWCoord}
  {ts : List ℤ}
-- given
  (h : Fin 6) :
-- imply
  (hexCSCoordPath c h ts).length = ts.length + 2 := by
-- proof
  apply StatMech.Universality.hexCSCoordPath_length c h ts

/--
[hexCSCoordPath_brick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSCoordPath_brick_eq
  {c : HexAWCoord}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hfit : HexCSHeadingFits c (hexCSHeadingFin h0))
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  (hexCSCoordPath c (hexCSHeadingFin h0) ts).map (fun q => hexBrickPos q - hexBrickPos c) = ons_pathVertices (hexCSBrickDirections h0 ts) := by
-- proof
  apply StatMech.Universality.hexCSCoordPath_brick c h0 ts hfit hlegal

/--
[hexCSCoordPath_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSCoordPath_pos_eq
  {c : HexAWCoord}
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hfit : HexCSHeadingFits c (hexCSHeadingFin h0))
  (hmid : m = hexAWMid c (hexCSEdgeOfHeading c (hexCSHeadingFin h0)))
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  (hexCSCoordPath c (hexCSHeadingFin h0) ts).map hexAWPos = hexAWPos c :: verticesAux m h0 ts := by
-- proof
  apply StatMech.Universality.hexCSCoordPath_pos c m h0 ts hfit hmid hlegal

/--
[hexCS_mem_of_two_incident_mids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_mem_of_two_incident_mids_eq
  {T L : ℕ}
  {c : HexAWCoord}
  {e f : Fin 3}
-- given
  (hef : e ≠ f)
  (he : hexAWMid c e ∈ hexCSMids T L)
  (hf : hexAWMid c f ∈ hexCSMids T L) :
-- imply
  c ∈ hexCSVertexSet T L := by
-- proof
  apply StatMech.Universality.hexCS_mem_of_two_incident_mids c e f hef he hf

/--
[hexCS_prefixCoord_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_prefixCoord_mem_eq
  {T L : ℕ}
  {hT : 0 < T}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion)
  (hk : k < ts.length) :
-- imply
  hexEndpointPrefixCoord ts hadm.1.1 k ∈ hexCSVertexSet T L := by
-- proof
  apply StatMech.Universality.hexCS_prefixCoord_mem ts hadm k hk

/--
[hexCS_endpointVertex_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_endpointVertex_inside_eq
  {T L : ℕ}
  {hT : 0 < T}
  {ts : List ℤ}
  {x : ℂ}
-- given
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion)
  (hx : x ∈ (ofTurns hexAWStart 1 ts).endpointVertices) :
-- imply
  ∃ c : HexAWCoord, c ∈ hexCSVertexSet T L ∧ x = hexAWPos c := by
-- proof
  apply StatMech.Universality.hexCS_endpointVertex_inside ts hadm x hx

/--
[hexCS_outer_ne_outsideStart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_outer_ne_outsideStart_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (hne : e ≠ hexCSStartIncidence T L hT) :
-- imply
  hexAWNeighbor e.vtx.1 e.edge ≠ hexCSOutsideStartCoord := by
-- proof
  apply StatMech.Universality.hexCS_outer_ne_outsideStart e hne

/--
[hexCS_full_isSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_full_isSAW_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  (ofTurns hexAWStart 1 ts).IsSAW := by
-- proof
  apply StatMech.Universality.hexCS_full_isSAW e ts he hne hadm

/--
[hexCS_outsideStart_not_mem_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_outsideStart_not_mem_vertices_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  hexAWPos hexCSOutsideStartCoord ∉ (ofTurns hexAWStart 1 ts).vertices := by
-- proof
  apply StatMech.Universality.hexCS_outsideStart_not_mem_vertices e ts he hne hadm

/--
[hexCSCoordPath_start_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSCoordPath_start_pos_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  (hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) ts).map hexAWPos = hexAWPos hexCSOutsideStartCoord :: verticesAux hexAWStart 1 ts := by
-- proof
  apply StatMech.Universality.hexCSCoordPath_start_pos ts hlegal

/--
[hexCSCoordPath_start_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSCoordPath_start_nodup_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  (hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) ts).Nodup := by
-- proof
  apply StatMech.Universality.hexCSCoordPath_start_nodup e ts he hne hadm

/--
[hexCSBrickDirections_vertices_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBrickDirections_vertices_nodup_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  (ons_pathVertices (hexCSBrickDirections 1 ts)).Nodup := by
-- proof
  apply StatMech.Universality.hexCSBrickDirections_vertices_nodup e ts he hne hadm

/--
[hexCSCoordPath_mem_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSCoordPath_mem_cases_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
  {q : HexAWCoord}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hq : q ∈ hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) ts) :
-- imply
  q = hexCSOutsideStartCoord ∨ q ∈ hexCSVertexSet T L ∨ q = hexAWNeighbor e.vtx.1 e.edge := by
-- proof
  apply StatMech.Universality.hexCSCoordPath_mem_cases e ts he hne hadm q hq

/--
[hexCS_inside_brick_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_inside_brick_bounds_eq
  {T L : ℕ}
  {c : HexAWCoord}
-- given
  (hc : c ∈ hexCSVertexSet T L) :
-- imply
  let R : ℤ := hexCSBrickRadius T L (-R < (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).1 ∧ (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).1 < R ∧ -R < (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).2 ∧ (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).2 < R) := by
-- proof
  apply StatMech.Universality.hexCS_inside_brick_bounds c hc

/--
[hexCS_periodicCoord_injective_of_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_periodicCoord_injective_of_slab_eq
  {l : List (Fin 4)}
  [NeZero l.length]
  {dx dy : ℤ}
-- given
  (hdisp : ons_pathDisplacement l = (dx, dy))
  (hdx : 0 < dx)
  (hnodup : (ons_pathVertices l).dropLast.Nodup)
  (hx : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1 ∧ z.1 < dx) :
-- imply
  Function.Injective (ons_periodStateCoord (fun i : Fin l.length => l.get i)) := by
-- proof
  apply StatMech.Universality.hexCS_periodicCoord_injective_of_slab l dx dy hdisp hdx hnodup hx

/--
[hexCS_cyclicTurnSum_eq_zero_of_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_cyclicTurnSum_eq_zero_of_slab_eq
  {l : List (Fin 4)}
  [NeZero l.length]
  {dx dy : ℤ}
-- given
  (hdisp : ons_pathDisplacement l = (dx, dy))
  (hdx : 0 < dx)
  (hnodup : (ons_pathVertices l).dropLast.Nodup)
  (hx : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1 ∧ z.1 < dx) :
-- imply
  ons_cyclicTurnSum l = 0 := by
-- proof
  apply StatMech.Universality.hexCS_cyclicTurnSum_eq_zero_of_slab l dx dy hdisp hdx hnodup hx

/--
[hexCS_periodicCoord_injective_of_negative_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_periodicCoord_injective_of_negative_slab_eq
  {l : List (Fin 4)}
  [NeZero l.length]
  {dx dy : ℤ}
-- given
  (hdisp : ons_pathDisplacement l = (dx, dy))
  (hdx : dx < 0)
  (hnodup : (ons_pathVertices l).dropLast.Nodup)
  (hx : ∀ z ∈ (ons_pathVertices l).dropLast, dx < z.1 ∧ z.1 ≤ 0) :
-- imply
  Function.Injective (ons_periodStateCoord (fun i : Fin l.length => l.get i)) := by
-- proof
  apply StatMech.Universality.hexCS_periodicCoord_injective_of_negative_slab l dx dy hdisp hdx hnodup hx

/--
[hexCS_cyclicTurnSum_eq_zero_of_negative_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_cyclicTurnSum_eq_zero_of_negative_slab_eq
  {l : List (Fin 4)}
  [NeZero l.length]
  {dx dy : ℤ}
-- given
  (hdisp : ons_pathDisplacement l = (dx, dy))
  (hdx : dx < 0)
  (hnodup : (ons_pathVertices l).dropLast.Nodup)
  (hx : ∀ z ∈ (ons_pathVertices l).dropLast, dx < z.1 ∧ z.1 ≤ 0) :
-- imply
  ons_cyclicTurnSum l = 0 := by
-- proof
  apply StatMech.Universality.hexCS_cyclicTurnSum_eq_zero_of_negative_slab l dx dy hdisp hdx hnodup hx

/--
[hexCSCoordPath_eq_prefixCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSCoordPath_eq_prefixCoords_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) ts = hexCSOutsideStartCoord :: List.ofFn (fun k : Fin (ts.length + 1) => hexEndpointPrefixCoord ts hlegal k.val) := by
-- proof
  apply StatMech.Universality.hexCSCoordPath_eq_prefixCoords ts hlegal

/--
[hexCS_finalPrefixCoord_eq_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_finalPrefixCoord_eq_outside_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  hexEndpointPrefixCoord ts hadm.1.1 ts.length = hexAWNeighbor e.vtx.1 e.edge := by
-- proof
  apply StatMech.Universality.hexCS_finalPrefixCoord_eq_outside e ts he hne hadm

/--
[hexCSOutsideStart_ne_endpointOutside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSOutsideStart_ne_endpointOutside_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT) :
-- imply
  hexCSOutsideStartCoord ≠ hexAWNeighbor e.vtx.1 e.edge := by
-- proof
  apply StatMech.Universality.hexCSOutsideStart_ne_endpointOutside e he hne

/--
[hexCSCoordPath_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSCoordPath_nodup_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  (hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) ts).Nodup := by
-- proof
  apply StatMech.Universality.hexCSCoordPath_nodup e ts he hne hadm

/--
[hexCSBrickDirections_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBrickDirections_displacement_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  ons_pathDisplacement (hexCSBrickDirections 1 ts) = hexCSEndDelta e := by
-- proof
  apply StatMech.Universality.hexCSBrickDirections_displacement e ts he hne hadm

/--
[hexCS_inside_brick_depth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_inside_brick_depth_pos_eq
  {T L : ℕ}
  {c : HexAWCoord}
-- given
  (hc : c ∈ hexCSVertexSet T L) :
-- imply
  0 < (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).2 - (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).1 := by
-- proof
  apply StatMech.Universality.hexCS_inside_brick_depth_pos c hc

/--
[hexCSEndDelta_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEndDelta_bounds_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  let R : ℤ := hexCSBrickRadius T L (-R < (hexCSEndDelta e).1 ∧ (hexCSEndDelta e).1 < R ∧ -R < (hexCSEndDelta e).2 ∧ (hexCSEndDelta e).2 < R) := by
-- proof
  apply StatMech.Universality.hexCSEndDelta_bounds e he

/--
[hexCSBrickDirections_dropLast_mem_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBrickDirections_dropLast_mem_cases_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
  {z : ℤ × ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hz : z ∈ (ons_pathVertices (hexCSBrickDirections 1 ts)).dropLast) :
-- imply
  z = 0 ∨ ∃ c : HexAWCoord, c ∈ hexCSVertexSet T L ∧ z = hexBrickPos c - hexBrickPos hexCSOutsideStartCoord := by
-- proof
  apply StatMech.Universality.hexCSBrickDirections_dropLast_mem_cases e ts he hne hadm z hz

/--
[hexCSSourceBelow_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceBelow_displacement_eq
  {R : ℕ} :
-- imply
  ons_pathDisplacement (hexCSSourceBelow R) = ((R : ℤ), (R : ℤ)) := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_displacement R

/--
[hexCSSourceAbove_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceAbove_displacement_eq
  {R : ℕ} :
-- imply
  ons_pathDisplacement (hexCSSourceAbove R) = ((R : ℤ), -(R : ℤ)) := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_displacement R

/--
[hexCSEastTail_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEastTail_displacement_eq
  {R : ℕ}
  {dx : ℤ}
-- given
  (h : dx ≤ R) :
-- imply
  ons_pathDisplacement (hexCSEastTail R dx) = ((R : ℤ) + 1 - dx, 0) := by
-- proof
  apply StatMech.Universality.hexCSEastTail_displacement R dx h

/--
[hexCSSouthEastTail_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSouthEastTail_displacement_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hx : dx ≤ R)
  (hy : -(R : ℤ) ≤ dy) :
-- imply
  ons_pathDisplacement (hexCSSouthEastTail R dx dy) = ((R : ℤ) + 1 - dx, -((R : ℤ) + dy)) := by
-- proof
  apply StatMech.Universality.hexCSSouthEastTail_displacement R dx dy hx hy

/--
[hexCSWestNorthEastTail_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSWestNorthEastTail_displacement_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hx : -(R : ℤ) ≤ dx)
  (hy : dy ≤ R) :
-- imply
  ons_pathDisplacement (hexCSWestNorthEastTail R dx dy) = ((R : ℤ) + 1 - dx, (R : ℤ) - dy) := by
-- proof
  apply StatMech.Universality.hexCSWestNorthEastTail_displacement R dx dy hx hy

/--
[hexCS_openTurn_three_replicates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_openTurn_three_replicates_eq
  {a b c : Fin 4}
  {na nb nc : ℕ} :
-- imply
  ons_openTurnSum (List.replicate (na + 1) a ++ List.replicate (nb + 1) b ++ List.replicate (nc + 1) c) = ons_turnPow a b + ons_turnPow b c := by
-- proof
  apply StatMech.Universality.hexCS_openTurn_three_replicates a b c na nb nc

/--
[hexCS_openTurn_two_replicates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_openTurn_two_replicates_eq
  {a b : Fin 4}
  {na nb : ℕ} :
-- imply
  ons_openTurnSum (List.replicate (na + 1) a ++ List.replicate (nb + 1) b) = ons_turnPow a b := by
-- proof
  apply StatMech.Universality.hexCS_openTurn_two_replicates a b na nb

/--
[hexCSSourceBelow_openTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceBelow_openTurn_eq
  {R : ℕ}
-- given
  (hR : 0 < R) :
-- imply
  ons_openTurnSum (hexCSSourceBelow R) = 2 := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_openTurn R hR

/--
[hexCSSourceAbove_openTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceAbove_openTurn_eq
  {R : ℕ}
-- given
  (hR : 0 < R) :
-- imply
  ons_openTurnSum (hexCSSourceAbove R) = -2 := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_openTurn R hR

/--
[hexCSEastTail_openTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEastTail_openTurn_eq
  {R : ℕ}
  {dx : ℤ} :
-- imply
  ons_openTurnSum (hexCSEastTail R dx) = 0 := by
-- proof
  apply StatMech.Universality.hexCSEastTail_openTurn R dx

/--
[hexCSWestNorthEastTail_openTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSWestNorthEastTail_openTurn_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hW : 0 < dx + R)
  (hN : 0 < (R : ℤ) - dy) :
-- imply
  ons_openTurnSum (hexCSWestNorthEastTail R dx dy) = -2 := by
-- proof
  apply StatMech.Universality.hexCSWestNorthEastTail_openTurn R dx dy hW hN

/--
[hexCSSouthEastTail_openTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSouthEastTail_openTurn_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hS : 0 < dy + R)
  (hE : 0 < (R : ℤ) - dx) :
-- imply
  ons_openTurnSum (hexCSSouthEastTail R dx dy) = 1 := by
-- proof
  apply StatMech.Universality.hexCSSouthEastTail_openTurn R dx dy hS hE

/--
[hexCSSourceBelow_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceBelow_vertices_dropLast_nodup_eq
  {R : ℕ} :
-- imply
  (ons_pathVertices (hexCSSourceBelow R)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_vertices_dropLast_nodup R

/--
[hexCSSourceAbove_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceAbove_vertices_dropLast_nodup_eq
  {R : ℕ} :
-- imply
  (ons_pathVertices (hexCSSourceAbove R)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_vertices_dropLast_nodup R

/--
[hexCSSourceBelow_vertex_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceBelow_vertex_cases_eq
  {R : ℕ}
  {z : ℤ × ℤ}
-- given
  (hz : z ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast) :
-- imply
  (∃ k : ℕ, k < 2 * R ∧ z = ((k : ℤ), 0)) ∨ (∃ k : ℕ, k < R ∧ z = (2 * (R : ℤ), (k : ℤ))) ∨ (∃ k : ℕ, k < R ∧ z = (2 * (R : ℤ) - (k : ℤ), (R : ℤ))) := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_vertex_cases R z hz

/--
[hexCSSourceAbove_vertex_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceAbove_vertex_cases_eq
  {R : ℕ}
  {z : ℤ × ℤ}
-- given
  (hz : z ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast) :
-- imply
  (∃ k : ℕ, k < 2 * R ∧ z = ((k : ℤ), 0)) ∨ (∃ k : ℕ, k < R ∧ z = (2 * (R : ℤ), -(k : ℤ))) ∨ (∃ k : ℕ, k < R ∧ z = (2 * (R : ℤ) - (k : ℤ), -(R : ℤ))) := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_vertex_cases R z hz

/--
[hexCSEastTail_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEastTail_vertices_dropLast_nodup_eq
  {R : ℕ}
  {dx : ℤ} :
-- imply
  (ons_pathVertices (hexCSEastTail R dx)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSEastTail_vertices_dropLast_nodup R dx

/--
[hexCSWestNorthEastTail_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSWestNorthEastTail_vertices_dropLast_nodup_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hW : 0 < dx + R)
  (hN : 0 < (R : ℤ) - dy) :
-- imply
  (ons_pathVertices (hexCSWestNorthEastTail R dx dy)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSWestNorthEastTail_vertices_dropLast_nodup R dx dy hW hN

/--
[hexCSSouthEastTail_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSouthEastTail_vertices_dropLast_nodup_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hS : 0 < dy + R) :
-- imply
  (ons_pathVertices (hexCSSouthEastTail R dx dy)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSSouthEastTail_vertices_dropLast_nodup R dx dy hS

/--
[hexCSEastTail_endpoint_vertex_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEastTail_endpoint_vertex_cases_eq
  {R : ℕ}
  {dx dy : ℤ}
  {z : ℤ × ℤ}
-- given
  (hz : z ∈ (ons_pathVertices (hexCSEastTail R dx)).dropLast) :
-- imply
  ∃ k : ℕ, k < ((R : ℤ) + 1 - dx).toNat ∧ (dx, dy) + z = (dx + k, dy) := by
-- proof
  apply StatMech.Universality.hexCSEastTail_endpoint_vertex_cases R dx dy z hz

/--
[hexCSWestNorthEastTail_endpoint_vertex_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSWestNorthEastTail_endpoint_vertex_cases_eq
  {R : ℕ}
  {dx dy : ℤ}
  {z : ℤ × ℤ}
-- given
  (hx : 0 ≤ dx + R)
  (hy : 0 ≤ (R : ℤ) - dy)
  (hz : z ∈ (ons_pathVertices (hexCSWestNorthEastTail R dx dy)).dropLast) :
-- imply
  (∃ k : ℕ, k < (dx + R).toNat ∧ (dx, dy) + z = (dx - k, dy)) ∨ (∃ k : ℕ, k < ((R : ℤ) - dy).toNat ∧ (dx, dy) + z = (-(R : ℤ), dy + k)) ∨ (∃ k : ℕ, k < 2 * R + 1 ∧ (dx, dy) + z = (-(R : ℤ) + k, (R : ℤ))) := by
-- proof
  apply StatMech.Universality.hexCSWestNorthEastTail_endpoint_vertex_cases R dx dy hx hy z hz

/--
[hexCSSouthEastTail_endpoint_vertex_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSouthEastTail_endpoint_vertex_cases_eq
  {R : ℕ}
  {dx dy : ℤ}
  {z : ℤ × ℤ}
-- given
  (hy : 0 ≤ dy + R)
  (hz : z ∈ (ons_pathVertices (hexCSSouthEastTail R dx dy)).dropLast) :
-- imply
  (∃ k : ℕ, k < (dy + R).toNat ∧ (dx, dy) + z = (dx, dy - k)) ∨ (∃ k : ℕ, k < ((R : ℤ) + 1 - dx).toNat ∧ (dx, dy) + z = (dx + k, -(R : ℤ))) := by
-- proof
  apply StatMech.Universality.hexCSSouthEastTail_endpoint_vertex_cases R dx dy hy z hz

/--
[hexCSEndDelta_left_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEndDelta_left_sign_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hc : e.vtx.1.color = .black)
  (hedge : e.edge = 0) :
-- imply
  (0 ≤ hexAWTrans e.vtx.1 → 0 < (hexCSEndDelta e).2) ∧ (¬ 0 ≤ hexAWTrans e.vtx.1 → (hexCSEndDelta e).2 < 0) := by
-- proof
  apply StatMech.Universality.hexCSEndDelta_left_sign e he hne hc hedge

/--
[hexCSEndDelta_slant_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEndDelta_slant_sign_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L) :
-- imply
  (e.vtx.1.color = .white ∧ e.edge = 1 → 0 < (hexCSEndDelta e).2) ∧ (e.vtx.1.color = .white ∧ e.edge = 2 → (hexCSEndDelta e).2 < 0) := by
-- proof
  apply StatMech.Universality.hexCSEndDelta_slant_sign e he

/--
[hexCSEndDelta_right_zero_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEndDelta_right_zero_height_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hc : e.vtx.1.color = .white)
  (hedge : e.edge = 0)
  (hy : (hexCSEndDelta e).2 = 0) :
-- imply
  (hexCSEndDelta e).1 < 0 := by
-- proof
  apply StatMech.Universality.hexCSEndDelta_right_zero_height e he hc hedge hy

/--
[hexCSEastRay_not_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEastRay_not_inside_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
  {c : HexAWCoord}
  {k : ℕ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hside : (e.vtx.1.color = .black ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = 0) ∨ (e.vtx.1.color = .white ∧ e.edge = 1 ∧ e.vtx.1.i = L))
  (hc : c ∈ hexCSVertexSet T L) :
-- imply
  hexBrickPos c - hexBrickPos hexCSOutsideStartCoord ≠ hexCSEndDelta e + ((k : ℤ), 0) := by
-- proof
  apply StatMech.Universality.hexCSEastRay_not_inside e he hside c hc k

/--
[hexCSWestRay_not_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSWestRay_not_inside_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
  {c : HexAWCoord}
  {k : ℕ}
-- given
  (hside : e.vtx.1.color = .white ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = T)
  (hc : c ∈ hexCSVertexSet T L) :
-- imply
  hexBrickPos c - hexBrickPos hexCSOutsideStartCoord ≠ hexCSEndDelta e + (-(k : ℤ), 0) := by
-- proof
  apply StatMech.Universality.hexCSWestRay_not_inside e hside c hc k

/--
[hexCSSouthRay_not_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSouthRay_not_inside_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
  {c : HexAWCoord}
  {k : ℕ}
-- given
  (hside : e.vtx.1.color = .white ∧ e.edge = 2 ∧ e.vtx.1.j = L)
  (hc : c ∈ hexCSVertexSet T L) :
-- imply
  hexBrickPos c - hexBrickPos hexCSOutsideStartCoord ≠ hexCSEndDelta e + (0, -(k : ℤ)) := by
-- proof
  apply StatMech.Universality.hexCSSouthRay_not_inside e hside c hc k

/--
[hexCS_three_piece_x_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_three_piece_x_slab_eq
  {P C S : List (Fin 4)}
  {D : ℤ}
-- given
  (hP : ∀ p ∈ (ons_pathVertices P).dropLast, 0 ≤ p.1 ∧ p.1 < D)
  (hC : ∀ c ∈ (ons_pathVertices C).dropLast, 0 ≤ (ons_pathDisplacement P + c).1 ∧ (ons_pathDisplacement P + c).1 < D)
  (hS : ∀ s ∈ (ons_pathVertices S).dropLast, 0 ≤ (ons_pathDisplacement P + ons_pathDisplacement C + s).1 ∧ (ons_pathDisplacement P + ons_pathDisplacement C + s).1 < D) :
-- imply
  ∀ z ∈ (ons_pathVertices (P ++ C ++ S)).dropLast, 0 ≤ z.1 ∧ z.1 < D := by
-- proof
  apply StatMech.Universality.hexCS_three_piece_x_slab P C S D hP hC hS

/--
[hexCSSourceBelow_x_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceBelow_x_slab_eq
  {R : ℕ} :
-- imply
  ∀ p ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast, 0 ≤ p.1 ∧ p.1 < (2 * R + 1 : ℕ) := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_x_slab R

/--
[hexCSSourceAbove_x_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceAbove_x_slab_eq
  {R : ℕ} :
-- imply
  ∀ p ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast, 0 ≤ p.1 ∧ p.1 < (2 * R + 1 : ℕ) := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_x_slab R

/--
[hexCS_central_x_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_central_x_slab_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  let R := hexCSBrickRadius T L ∀ c ∈ (ons_pathVertices (hexCSBrickDirections 1 ts)).dropLast, 0 ≤ (((R : ℤ), 0) + c).1 ∧ (((R : ℤ), 0) + c).1 < (((2 * R + 1 : ℕ) : ℤ)) := by
-- proof
  apply StatMech.Universality.hexCS_central_x_slab e ts he hne hadm

/--
[hexCSEastTail_x_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEastTail_x_slab_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hxlo : -(R : ℤ) < dx)
  (hxhi : dx < R) :
-- imply
  ∀ s ∈ (ons_pathVertices (hexCSEastTail R dx)).dropLast, 0 ≤ (((R : ℤ), 0) + (dx, dy) + s).1 ∧ (((R : ℤ), 0) + (dx, dy) + s).1 < (((2 * R + 1 : ℕ) : ℤ)) := by
-- proof
  apply StatMech.Universality.hexCSEastTail_x_slab R dx dy hxlo hxhi

/--
[hexCSWestNorthEastTail_x_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSWestNorthEastTail_x_slab_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hxlo : -(R : ℤ) < dx)
  (hxhi : dx < R)
  (hyhi : dy < R) :
-- imply
  ∀ s ∈ (ons_pathVertices (hexCSWestNorthEastTail R dx dy)).dropLast, 0 ≤ (((R : ℤ), 0) + (dx, dy) + s).1 ∧ (((R : ℤ), 0) + (dx, dy) + s).1 < (((2 * R + 1 : ℕ) : ℤ)) := by
-- proof
  apply StatMech.Universality.hexCSWestNorthEastTail_x_slab R dx dy hxlo hxhi hyhi

/--
[hexCSSouthEastTail_x_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSouthEastTail_x_slab_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hxlo : -(R : ℤ) < dx)
  (hxhi : dx < R)
  (hylo : -(R : ℤ) < dy) :
-- imply
  ∀ s ∈ (ons_pathVertices (hexCSSouthEastTail R dx dy)).dropLast, 0 ≤ (((R : ℤ), 0) + (dx, dy) + s).1 ∧ (((R : ℤ), 0) + (dx, dy) + s).1 < (((2 * R + 1 : ℕ) : ℤ)) := by
-- proof
  apply StatMech.Universality.hexCSSouthEastTail_x_slab R dx dy hxlo hxhi hylo

/--
[hexCS_three_piece_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_three_piece_vertices_dropLast_nodup_eq
  {P C S : List (Fin 4)}
-- given
  (hP : (ons_pathVertices P).dropLast.Nodup)
  (hC : (ons_pathVertices C).dropLast.Nodup)
  (hS : (ons_pathVertices S).dropLast.Nodup)
  (hPC : ∀ p ∈ (ons_pathVertices P).dropLast, ∀ c ∈ (ons_pathVertices C).dropLast, p ≠ ons_pathDisplacement P + c)
  (hPS : ∀ p ∈ (ons_pathVertices P).dropLast, ∀ s ∈ (ons_pathVertices S).dropLast, p ≠ ons_pathDisplacement P + ons_pathDisplacement C + s)
  (hCS : ∀ c ∈ (ons_pathVertices C).dropLast, ∀ s ∈ (ons_pathVertices S).dropLast, ons_pathDisplacement P + c ≠ ons_pathDisplacement P + ons_pathDisplacement C + s) :
-- imply
  (ons_pathVertices (P ++ C ++ S)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCS_three_piece_vertices_dropLast_nodup P C S hP hC hS hPC hPS hCS

/--
[hexCSSourceBelow_central_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceBelow_central_disjoint_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  let R := hexCSBrickRadius T L ∀ p ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast, ∀ c ∈ (ons_pathVertices (hexCSBrickDirections 1 ts)).dropLast, p ≠ ons_pathDisplacement (hexCSSourceBelow R) + c := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_central_disjoint e ts he hne hadm

/--
[hexCSSourceAbove_central_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceAbove_central_disjoint_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  let R := hexCSBrickRadius T L ∀ p ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast, ∀ c ∈ (ons_pathVertices (hexCSBrickDirections 1 ts)).dropLast, p ≠ ons_pathDisplacement (hexCSSourceAbove R) + c := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_central_disjoint e ts he hne hadm

/--
[hexCSBelowEastPeriod_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBelowEastPeriod_vertices_dropLast_nodup_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hside : (e.vtx.1.color = .black ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = 0) ∨ (e.vtx.1.color = .white ∧ e.edge = 1 ∧ e.vtx.1.i = L))
  (hdy : 0 < (hexCSEndDelta e).2) :
-- imply
  let R := hexCSBrickRadius T L let C := hexCSBrickDirections 1 ts (ons_pathVertices (hexCSSourceBelow R ++ C ++ hexCSEastTail R (hexCSEndDelta e).1)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSBelowEastPeriod_vertices_dropLast_nodup e ts he hne hadm hside hdy

/--
[hexCSAboveEastPeriod_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSAboveEastPeriod_vertices_dropLast_nodup_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hside : e.vtx.1.color = .black ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = 0)
  (hdy : (hexCSEndDelta e).2 < 0) :
-- imply
  let R := hexCSBrickRadius T L let C := hexCSBrickDirections 1 ts (ons_pathVertices (hexCSSourceAbove R ++ C ++ hexCSEastTail R (hexCSEndDelta e).1)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSAboveEastPeriod_vertices_dropLast_nodup e ts he hne hadm hside hdy

/--
[hexCSRightPeriod_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSRightPeriod_vertices_dropLast_nodup_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hside : e.vtx.1.color = .white ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = T) :
-- imply
  let R := hexCSBrickRadius T L let C := hexCSBrickDirections 1 ts (ons_pathVertices (hexCSSourceBelow R ++ C ++ hexCSWestNorthEastTail R (hexCSEndDelta e).1 (hexCSEndDelta e).2)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSRightPeriod_vertices_dropLast_nodup e ts he hne hadm hside

/--
[hexCSLowerPeriod_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSLowerPeriod_vertices_dropLast_nodup_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hside : e.vtx.1.color = .white ∧ e.edge = 2 ∧ e.vtx.1.j = L) :
-- imply
  let R := hexCSBrickRadius T L let C := hexCSBrickDirections 1 ts (ons_pathVertices (hexCSSourceAbove R ++ C ++ hexCSSouthEastTail R (hexCSEndDelta e).1 (hexCSEndDelta e).2)).dropLast.Nodup := by
-- proof
  apply StatMech.Universality.hexCSLowerPeriod_vertices_dropLast_nodup e ts he hne hadm hside

/--
[hexCSBelowEastPeriod_cyclicTurnSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSBelowEastPeriod_cyclicTurnSum_eq_zero_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hside : (e.vtx.1.color = .black ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = 0) ∨ (e.vtx.1.color = .white ∧ e.edge = 1 ∧ e.vtx.1.i = L))
  (hdy : 0 < (hexCSEndDelta e).2) :
-- imply
  let R := hexCSBrickRadius T L let C := hexCSBrickDirections 1 ts ons_cyclicTurnSum (hexCSSourceBelow R ++ C ++ hexCSEastTail R (hexCSEndDelta e).1) = 0 := by
-- proof
  apply StatMech.Universality.hexCSBelowEastPeriod_cyclicTurnSum_eq_zero e ts he hne hadm hside hdy

/--
[hexCSAboveEastPeriod_cyclicTurnSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSAboveEastPeriod_cyclicTurnSum_eq_zero_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hside : e.vtx.1.color = .black ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = 0)
  (hdy : (hexCSEndDelta e).2 < 0) :
-- imply
  let R := hexCSBrickRadius T L let C := hexCSBrickDirections 1 ts ons_cyclicTurnSum (hexCSSourceAbove R ++ C ++ hexCSEastTail R (hexCSEndDelta e).1) = 0 := by
-- proof
  apply StatMech.Universality.hexCSAboveEastPeriod_cyclicTurnSum_eq_zero e ts he hne hadm hside hdy

/--
[hexCSRightPeriod_cyclicTurnSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSRightPeriod_cyclicTurnSum_eq_zero_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hside : e.vtx.1.color = .white ∧ e.edge = 0 ∧ hexAWDepth e.vtx.1 = T) :
-- imply
  let R := hexCSBrickRadius T L let C := hexCSBrickDirections 1 ts ons_cyclicTurnSum (hexCSSourceBelow R ++ C ++ hexCSWestNorthEastTail R (hexCSEndDelta e).1 (hexCSEndDelta e).2) = 0 := by
-- proof
  apply StatMech.Universality.hexCSRightPeriod_cyclicTurnSum_eq_zero e ts he hne hadm hside

/--
[hexCSLowerPeriod_cyclicTurnSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSLowerPeriod_cyclicTurnSum_eq_zero_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge))
  (hside : e.vtx.1.color = .white ∧ e.edge = 2 ∧ e.vtx.1.j = L) :
-- imply
  let R := hexCSBrickRadius T L let C := hexCSBrickDirections 1 ts ons_cyclicTurnSum (hexCSSourceAbove R ++ C ++ hexCSSouthEastTail R (hexCSEndDelta e).1 (hexCSEndDelta e).2) = 0 := by
-- proof
  apply StatMech.Universality.hexCSLowerPeriod_cyclicTurnSum_eq_zero e ts he hne hadm hside

/--
[hexCSSourceBelow_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceBelow_ne_nil_eq
  {R : ℕ}
-- given
  (hR : 0 < R) :
-- imply
  hexCSSourceBelow R ≠ [] := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_ne_nil R hR

/--
[hexCSSourceAbove_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceAbove_ne_nil_eq
  {R : ℕ}
-- given
  (hR : 0 < R) :
-- imply
  hexCSSourceAbove R ≠ [] := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_ne_nil R hR

/--
[hexCSSourceBelow_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceBelow_head_eq
  {R : ℕ}
-- given
  (hR : 0 < R) :
-- imply
  (hexCSSourceBelow R).head! = 0 := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_head R hR

/--
[hexCSSourceAbove_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceAbove_head_eq
  {R : ℕ}
-- given
  (hR : 0 < R) :
-- imply
  (hexCSSourceAbove R).head! = 0 := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_head R hR

/--
[hexCSSourceBelow_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceBelow_getLast_eq
  {R : ℕ}
-- given
  (hR : 0 < R) :
-- imply
  (hexCSSourceBelow R).getLast! = 2 := by
-- proof
  apply StatMech.Universality.hexCSSourceBelow_getLast R hR

/--
[hexCSSourceAbove_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSourceAbove_getLast_eq
  {R : ℕ}
-- given
  (hR : 0 < R) :
-- imply
  (hexCSSourceAbove R).getLast! = 2 := by
-- proof
  apply StatMech.Universality.hexCSSourceAbove_getLast R hR

/--
[hexCSEastTail_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEastTail_ne_nil_eq
  {R : ℕ}
  {dx : ℤ}
-- given
  (h : 0 < (R : ℤ) + 1 - dx) :
-- imply
  hexCSEastTail R dx ≠ [] := by
-- proof
  apply StatMech.Universality.hexCSEastTail_ne_nil R dx h

/--
[hexCSEastTail_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEastTail_head_eq
  {R : ℕ}
  {dx : ℤ}
-- given
  (h : 0 < (R : ℤ) + 1 - dx) :
-- imply
  (hexCSEastTail R dx).head! = 0 := by
-- proof
  apply StatMech.Universality.hexCSEastTail_head R dx h

/--
[hexCSEastTail_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSEastTail_getLast_eq
  {R : ℕ}
  {dx : ℤ}
-- given
  (h : 0 < (R : ℤ) + 1 - dx) :
-- imply
  (hexCSEastTail R dx).getLast! = 0 := by
-- proof
  apply StatMech.Universality.hexCSEastTail_getLast R dx h

/--
[hexCSWestNorthEastTail_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSWestNorthEastTail_ne_nil_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hW : 0 < dx + R) :
-- imply
  hexCSWestNorthEastTail R dx dy ≠ [] := by
-- proof
  apply StatMech.Universality.hexCSWestNorthEastTail_ne_nil R dx dy hW

/--
[hexCSWestNorthEastTail_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSWestNorthEastTail_head_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hW : 0 < dx + R) :
-- imply
  (hexCSWestNorthEastTail R dx dy).head! = 2 := by
-- proof
  apply StatMech.Universality.hexCSWestNorthEastTail_head R dx dy hW

/--
[hexCSWestNorthEastTail_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSWestNorthEastTail_getLast_eq
  {R : ℕ}
  {dx dy : ℤ} :
-- imply
  (hexCSWestNorthEastTail R dx dy).getLast! = 0 := by
-- proof
  apply StatMech.Universality.hexCSWestNorthEastTail_getLast R dx dy

/--
[hexCSSouthEastTail_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSouthEastTail_ne_nil_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hS : 0 < dy + R) :
-- imply
  hexCSSouthEastTail R dx dy ≠ [] := by
-- proof
  apply StatMech.Universality.hexCSSouthEastTail_ne_nil R dx dy hS

/--
[hexCSSouthEastTail_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSouthEastTail_head_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hS : 0 < dy + R) :
-- imply
  (hexCSSouthEastTail R dx dy).head! = 3 := by
-- proof
  apply StatMech.Universality.hexCSSouthEastTail_head R dx dy hS

/--
[hexCSSouthEastTail_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCSSouthEastTail_getLast_eq
  {R : ℕ}
  {dx dy : ℤ}
-- given
  (hE : 0 < (R : ℤ) + 1 - dx) :
-- imply
  (hexCSSouthEastTail R dx dy).getLast! = 0 := by
-- proof
  apply StatMech.Universality.hexCSSouthEastTail_getLast R dx dy hE

/--
[hexCS_cyclicTurnSum_three_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_cyclicTurnSum_three_piece_eq
  {P C S : List (Fin 4)}
-- given
  (hP : P ≠ [])
  (hC : C ≠ [])
  (hS : S ≠ [])
  (hPhead : P.head! = 0)
  (hPlast : P.getLast! = 2)
  (hChead : C.head! = 2)
  (hjoin : C.getLast! = S.head!)
  (hSlast : S.getLast! = 0) :
-- imply
  ons_cyclicTurnSum (P ++ C ++ S) = ons_openTurnSum P + ons_openTurnSum C + ons_openTurnSum S := by
-- proof
  apply StatMech.Universality.hexCS_cyclicTurnSum_three_piece P C S hP hC hS hPhead hPlast hChead hjoin hSlast

/--
[hexCS_boundaryWindowLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean)
-/
@[path]
private lemma hexCS_boundaryWindowLaw_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  HexCSBoundaryWindowLaw T L hT := by
-- proof
  apply StatMech.Universality.hexCS_boundaryWindowLaw T L hT


-- created on 2026-10-23
