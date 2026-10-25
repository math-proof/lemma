import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
open StatMech StatMech.Universality


/--
[hexEndpoint_vertexPos_ne_of_saw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_vertexPos_ne_of_saw_eq
  {ts : List ℤ}
  {i j : ℕ}
-- given
  (hsaw : (ofTurns hexAWStart 1 ts).EndpointIsSAW)
  (hi : i < ts.length)
  (hj : j < ts.length)
  (hne : i ≠ j) :
-- imply
  hexJordan_vertexPos hexAWStart 1 ts i ≠ hexJordan_vertexPos hexAWStart 1 ts j := by
-- proof
  apply StatMech.Universality.hexEndpoint_vertexPos_ne_of_saw ts hsaw i j hi hj hne

/--
[hexEndpoint_vertexPos_eq_nextMid_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_vertexPos_eq_nextMid_sub_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hk : k < ts.length) :
-- imply
  hexJordan_vertexPos hexAWStart 1 ts k = hexInfra_midAccum hexAWStart 1 (ts.take (k + 1)) - halfStep (hexInfra_headAccum 1 (ts.take (k + 1))) := by
-- proof
  apply StatMech.Universality.hexEndpoint_vertexPos_eq_nextMid_sub ts k hk

/--
[hexEndpoint_edge_endpoint_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_edge_endpoint_cases_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {e : Fin 3}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e) :
-- imply
  (hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos c ∧ hexInfra_midAccum hexAWStart 1 ts - halfStep (hexInfra_headAccum 1 ts) = hexAWPos (hexAWNeighbor c e)) ∨ (hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos (hexAWNeighbor c e) ∧ hexInfra_midAccum hexAWStart 1 ts - halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) := by
-- proof
  apply StatMech.Universality.hexEndpoint_edge_endpoint_cases ts c e hlegal hmid

/--
[hexEndpoint_final_mid_fresh_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_final_mid_fresh_aw_eq
  {base : List ℤ}
  {t : ℤ}
  {c : HexAWCoord}
  {e : Fin 3}
-- given
  (hlegal : (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
  (hne : hexAWMid c e ≠ hexAWStart) :
-- imply
  ¬PassesThrough hexAWStart 1 base (hexAWMid c e) := by
-- proof
  apply StatMech.Universality.hexEndpoint_final_mid_fresh_aw base t c e hlegal hend hne

/--
[hexAWMid_edge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexAWMid_edge_injective_eq
  {c : HexAWCoord} :
-- imply
  Function.Injective (hexAWMid c) := by
-- proof
  apply StatMech.Universality.hexAWMid_edge_injective c

/--
[hexEndpoint_count_two_other_base_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_count_two_other_base_mid_eq
  {base : List ℤ}
  {t : ℤ}
  {c : HexAWCoord}
  {e : Fin 3}
-- given
  (hend : (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
  (hnew : ¬PassesThrough hexAWStart 1 base (hexAWMid c e))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) (base ++ [t]) = 2) :
-- imply
  ∃ f : Fin 3, f ≠ e ∧ PassesThrough hexAWStart 1 base (hexAWMid c f) := by
-- proof
  apply StatMech.Universality.hexEndpoint_count_two_other_base_mid base t c e hend hnew hcount

/--
[hexAW_specialMidCount_three_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexAW_specialMidCount_three_of_all_eq
  {ts : List ℤ}
  {c : HexAWCoord}
-- given
  (hall : ∀ e : Fin 3, PassesThrough hexAWStart 1 ts (hexAWMid c e)) :
-- imply
  specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3 := by
-- proof
  apply StatMech.Universality.hexAW_specialMidCount_three_of_all ts c hall

/--
[hexAW_all_mids_of_specialMidCount_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexAW_all_mids_of_specialMidCount_three_eq
  {ts : List ℤ}
  {c : HexAWCoord}
-- given
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  ∀ e : Fin 3, PassesThrough hexAWStart 1 ts (hexAWMid c e) := by
-- proof
  apply StatMech.Universality.hexAW_all_mids_of_specialMidCount_three ts c hcount

/--
[hexEndpoint_passes_iff_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_passes_iff_prefix_eq
  {ts : List ℤ}
  {z : ℂ} :
-- imply
  PassesThrough hexAWStart 1 ts z ↔ ∃ k, k ≤ ts.length ∧ hexInfra_midAccum hexAWStart 1 (ts.take k) = z := by
-- proof
  apply StatMech.Universality.hexEndpoint_passes_iff_prefix ts z

/--
[hexEndpoint_local_crossing_of_internal_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_local_crossing_of_internal_mid_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {e : Fin 3}
  {k : ℕ}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hk : k < ts.length)
  (hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) = hexAWMid c e) :
-- imply
  Nonempty (HexEndpointLocalCrossing ts c) := by
-- proof
  apply StatMech.Universality.hexEndpoint_local_crossing_of_internal_mid ts c e k hnotOutside hlegal hk hmid

/--
[hexEndpoint_local_crossing_of_count_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_local_crossing_of_count_three_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  Nonempty (HexEndpointLocalCrossing ts c) := by
-- proof
  apply StatMech.Universality.hexEndpoint_local_crossing_of_count_three ts c endEdge hnotOutside hlegal hend hcount

/--
[HexEndpointLocalCrossing.internal_index_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma internal_index_cases_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {e : Fin 3}
  {k : ℕ}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hk : k < ts.length)
  (hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) = hexAWMid c e) :
-- imply
  k = C.index ∨ k = C.index + 1 := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.internal_index_cases C hnotOutside hlegal e k hk hmid

/--
[HexEndpointLocalCrossing.exists_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma exists_third_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c} :
-- imply
  ∃ e : Fin 3, e ≠ C.before ∧ e ≠ C.after := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.exists_third C

/--
[HexEndpointLocalCrossing.endEdge_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma endEdge_ne_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  endEdge ≠ C.before ∧ endEdge ≠ C.after := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.endEdge_ne C hnotOutside hlegal endEdge hend hcount

/--
[HexEndpointLocalCrossing.endpoint_lookahead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma endpoint_lookahead_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.endpoint_lookahead C hnotOutside hlegal endEdge hend hcount

/--
[hexEndpoint_kTwo_last_vertex_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_kTwo_last_vertex_aw_eq
  {base : List ℤ}
  {t : ℤ}
  {c : HexAWCoord}
  {e : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
  (hneStart : hexAWMid c e ≠ hexAWStart)
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) (base ++ [t]) = 2) :
-- imply
  hexInfra_midAccum hexAWStart 1 base + halfStep (hexInfra_headAccum 1 base) = hexAWPos c := by
-- proof
  apply StatMech.Universality.hexEndpoint_kTwo_last_vertex_aw base t c e hnotOutside hlegal hend hneStart hcount

/--
[hexEndpoint_count_one_forward_vertex_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_count_one_forward_vertex_aw_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {e : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c e))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 1) :
-- imply
  hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
-- proof
  apply StatMech.Universality.hexEndpoint_count_one_forward_vertex_aw ts c e hnotOutside hlegal hend hcount

/--
[hexEndpoint_kTwo_mem_cyclicTriplet_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpoint_kTwo_mem_cyclicTriplet_aw_eq
  {region : ℂ → Prop}
  {c : HexAWCoord}
  {e : Fin 3}
  {base : List ℤ}
  {t : ℤ}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hneStart : hexAWMid c e ≠ hexAWStart)
  (hvalid : (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 (base ++ [t])).StaysIn region ∧ (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) (base ++ [t]) = 2)
  (hall : ∀ f : Fin 3, region (hexAWMid c f)) :
-- imply
  ∃ C : HexEndpointCyclicTriplet region hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c), base ++ [t] ∈ C.piece ∧ C.base = base := by
-- proof
  apply StatMech.Universality.hexEndpoint_kTwo_mem_cyclicTriplet_aw c e base t hnotOutside hneStart hvalid hcount hall

/--
[hexEndpointLoopPartner_eq_anchored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpointLoopPartner_eq_anchored_eq
  {L : List ℤ} :
-- imply
  hexEndpointLoopPartner L = anchoredLoopReverse L := by
-- proof
  apply StatMech.Universality.hexEndpointLoopPartner_eq_anchored L

/--
[hexEndpointLoopPartner_length_of_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpointLoopPartner_length_of_ne_nil_eq
  {L : List ℤ}
-- given
  (hL : L ≠ []) :
-- imply
  (hexEndpointLoopPartner L).length = L.length := by
-- proof
  apply StatMech.Universality.hexEndpointLoopPartner_length_of_ne_nil L hL

/--
[hexEndpointLoopPartner_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpointLoopPartner_sum_eq
  {L : List ℤ}
-- given
  (hfirst : ∃ tail, L = 1 :: tail)
  (hsum : L.sum = -4) :
-- imply
  (hexEndpointLoopPartner L).sum = 4 := by
-- proof
  apply StatMech.Universality.hexEndpointLoopPartner_sum L hfirst hsum

/--
[hexEndpointLoopPartner_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpointLoopPartner_involutive_eq
  {L : List ℤ} :
-- imply
  hexEndpointLoopPartner (hexEndpointLoopPartner L) = L := by
-- proof
  apply StatMech.Universality.hexEndpointLoopPartner_involutive L

/--
[HexEndpointCyclicLoopPair.contribution_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma contribution_zero_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {P : HexEndpointCyclicLoopPair region a h0 v du} :
-- imply
  (labelMid v du (hexCyclicSucc P.baseLabel) - v) * endpointParafSummand region a h0 (labelMid v du (hexCyclicSucc P.baseLabel)) (5 / 8) hexChi (P.base ++ P.loopQ) + (labelMid v du (hexCyclicPred P.baseLabel) - v) * endpointParafSummand region a h0 (labelMid v du (hexCyclicPred P.baseLabel)) (5 / 8) hexChi (P.base ++ hexEndpointLoopPartner P.loopQ) = 0 := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicLoopPair.contribution_zero P

/--
[HexEndpointCyclicLoopPair.sum_piece_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma sum_piece_zero_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {P : HexEndpointCyclicLoopPair region a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  ∑ ts ∈ P.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicLoopPair.sum_piece_zero hdu P

/--
[hexEndpointPrefixCoord_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpointPrefixCoord_pos_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  hexJordan_vertexPos hexAWStart 1 ts k = hexAWPos (hexEndpointPrefixCoord ts hlegal k) := by
-- proof
  apply StatMech.Universality.hexEndpointPrefixCoord_pos ts hlegal k

/--
[hexEndpointPrefixCoord_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma hexEndpointPrefixCoord_adjacent_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hk : k < ts.length) :
-- imply
  ∃ e : Fin 3, hexAWNeighbor (hexEndpointPrefixCoord ts hlegal k) e = hexEndpointPrefixCoord ts hlegal (k + 1) := by
-- proof
  apply StatMech.Universality.hexEndpointPrefixCoord_adjacent ts hlegal k hk

/--
[HexEndpointLocalCrossing.loopLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma loopLength_pos_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c} :
-- imply
  0 < C.loopLength := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.loopLength_pos C

/--
[HexEndpointLocalCrossing.loopCoords_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma loopCoords_length_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  (C.loopCoords hlegal).length = C.loopLength := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.loopCoords_length C hlegal

/--
[HexEndpointLocalCrossing.loopCoord_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma loopCoord_injective_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
-- imply
  Function.Injective (C.loopCoord hlegal.1) := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.loopCoord_injective C hlegal

/--
[HexEndpointLocalCrossing.loopCoords_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma loopCoords_nodup_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
-- imply
  (C.loopCoords hlegal.1).Nodup := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.loopCoords_nodup C hlegal

/--
[HexEndpointLocalCrossing.loopCoord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma loopCoord_zero_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  [NeZero C.loopLength]
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  C.loopCoord hlegal 0 = c := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.loopCoord_zero C hlegal

/--
[HexEndpointLocalCrossing.finalPrefixCoord_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma finalPrefixCoord_eq_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  hexEndpointPrefixCoord ts hlegal.1 ts.length = c := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.finalPrefixCoord_eq C hnotOutside hlegal endEdge hend hcount

/--
[HexEndpointLocalCrossing.loopCoord_cyclic_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean)
-/
@[path]
private lemma loopCoord_cyclic_adjacent_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {C : HexEndpointLocalCrossing ts c}
  {endEdge : Fin 3}
  [NeZero C.loopLength]
  {i : Fin C.loopLength}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
  (hcount : specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 3) :
-- imply
  ∃ e : Fin 3, hexAWNeighbor (C.loopCoord hlegal.1 i) e = C.loopCoord hlegal.1 (i + 1) := by
-- proof
  apply StatMech.Universality.HexEndpointLocalCrossing.loopCoord_cyclic_adjacent C hnotOutside hlegal endEdge hend hcount i


-- created on 2026-10-23
