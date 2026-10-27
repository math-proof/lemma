import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
open StatMech StatMech.Universality StatMech.Universality.HexFiniteRegion


/--
[hexEndpointCoordRun_base_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpointCoordRun_base_compatible_eq :
-- imply
  (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base []).ColorCompatible := by
-- proof
  apply StatMech.Universality.hexEndpointCoordRun_base_compatible

/--
[hexEndpointCoordRun_step_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpointCoordRun_step_compatible_eq
  {p d : HexReturnCoord}
  {t : ℤ}
-- given
  (hc : (HexEndpointCoordRun.mk p d).ColorCompatible)
  (ht : t = 1 ∨ t = -1) :
-- imply
  (HexEndpointCoordRun.mk (p.add (d.turn t)) (d.turn t)).ColorCompatible := by
-- proof
  apply StatMech.Universality.hexEndpointCoordRun_step_compatible p d t hc ht

/--
[hexEndpointCoordRun_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpointCoordRun_compatible_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hc : (HexEndpointCoordRun.mk p d).ColorCompatible)
  (hunit : d.IsUnit)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  (hexEndpointCoordRun p d ts).ColorCompatible := by
-- proof
  apply StatMech.Universality.hexEndpointCoordRun_compatible p d ts hc hunit hlegal

/--
[hexEndpointCoordRun_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpointCoordRun_geometry_eq
  {p d : HexReturnCoord}
  {m s : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ)
  (hdir : halfStep h = d.value * s)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  let r := hexEndpointCoordRun p d ts hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) = m + halfStep h + 2 * ((r.pos.value - p.value) * s) ∧ halfStep (hexInfra_headAccum h ts) = r.dir.value * s := by
-- proof
  apply StatMech.Universality.hexEndpointCoordRun_geometry p d m s h ts hdir hlegal

/--
[hexEndpoint_return_even_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_return_even_direction_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hreturn : hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) = m + halfStep h) :
-- imply
  (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).dir.IsEvenDir := by
-- proof
  apply StatMech.Universality.hexEndpoint_return_even_direction m h ts hlegal hreturn

/--
[hexEndpoint_halfStep_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_halfStep_add_two_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h + 2) = hexOmega * halfStep h := by
-- proof
  apply StatMech.Universality.hexEndpoint_halfStep_add_two h

/--
[hexEndpoint_halfStep_add_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_halfStep_add_four_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h + 4) = hexOmega ^ 2 * halfStep h := by
-- proof
  apply StatMech.Universality.hexEndpoint_halfStep_add_four h

/--
[hexEndpoint_halfStep_add_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_halfStep_add_six_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h + 6) = halfStep h := by
-- proof
  apply StatMech.Universality.hexEndpoint_halfStep_add_six h

/--
[hexEndpoint_halfStep_add_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_halfStep_add_three_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h + 3) = -halfStep h := by
-- proof
  apply StatMech.Universality.hexEndpoint_halfStep_add_three h

/--
[hexEndpoint_halfStep_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_halfStep_sub_one_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h - 1) = -(hexOmega * halfStep h) := by
-- proof
  apply StatMech.Universality.hexEndpoint_halfStep_sub_one h

/--
[hexEndpoint_halfStep_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_halfStep_add_one_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h + 1) = -(hexOmega ^ 2 * halfStep h) := by
-- proof
  apply StatMech.Universality.hexEndpoint_halfStep_add_one h

/--
[hexAW_halfStep_edge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexAW_halfStep_edge_one_eq
  {c : HexAWCoord} :
-- imply
  halfStep (hexAWHeading c 1) = hexOmega * halfStep (hexAWHeading c 0) := by
-- proof
  apply StatMech.Universality.hexAW_halfStep_edge_one c

/--
[hexAW_halfStep_edge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexAW_halfStep_edge_two_eq
  {c : HexAWCoord} :
-- imply
  halfStep (hexAWHeading c 2) = hexOmega ^ 2 * halfStep (hexAWHeading c 0) := by
-- proof
  apply StatMech.Universality.hexAW_halfStep_edge_two c

/--
[hexAWMid_sub_pos_eq_halfStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexAWMid_sub_pos_eq_halfStep_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexAWMid c e - hexAWPos c = halfStep (hexAWHeading c e) := by
-- proof
  apply StatMech.Universality.hexAWMid_sub_pos_eq_halfStep c e

/--
[hexAW_labelMid_eq_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexAW_labelMid_eq_mid_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c) e = hexAWMid c e := by
-- proof
  apply StatMech.Universality.hexAW_labelMid_eq_mid c e

/--
[hexAW_base_du_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexAW_base_du_ne_zero_eq
  {c : HexAWCoord} :
-- imply
  hexAWMid c 0 - hexAWPos c ≠ 0 := by
-- proof
  apply StatMech.Universality.hexAW_base_du_ne_zero c

/--
[hexAWPos_eq_returnPos_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexAWPos_eq_returnPos_mul_eq
  {c : HexAWCoord} :
-- imply
  hexAWPos c = (hexAWReturnPos c).value * hexUnit 1 := by
-- proof
  apply StatMech.Universality.hexAWPos_eq_returnPos_mul c

/--
[hexAW_two_mul_mid_eq_returnMidSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexAW_two_mul_mid_eq_returnMidSum_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  (2 : ℂ) * hexAWMid c e = (hexAWReturnMidSum c e).value * hexUnit 1 := by
-- proof
  apply StatMech.Universality.hexAW_two_mul_mid_eq_returnMidSum c e

/--
[HexReturnCoord.value_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma value_injective_eq :
-- imply
  Function.Injective HexReturnCoord.value := by
-- proof
  apply StatMech.Universality.HexReturnCoord.value_injective

/--
[hexAWPos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexAWPos_injective_eq :
-- imply
  Function.Injective hexAWPos := by
-- proof
  apply StatMech.Universality.hexAWPos_injective

/--
[hexAWMid_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexAWMid_eq_iff_eq
  {c d : HexAWCoord}
  {e f : Fin 3} :
-- imply
  hexAWMid c e = hexAWMid d f ↔ (d = c ∧ f = e) ∨ (d = hexAWNeighbor c e ∧ f = e) := by
-- proof
  apply StatMech.Universality.hexAWMid_eq_iff c d e f

/--
[hexEndpoint_vertex_eq_runPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_vertex_eq_runPos_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos.value * hexUnit 1 := by
-- proof
  apply StatMech.Universality.hexEndpoint_vertex_eq_runPos ts hlegal

/--
[hexEndpointCoordRun_pos_exists_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpointCoordRun_pos_exists_aw_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  ∃ c : HexAWCoord, (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos = hexAWReturnPos c := by
-- proof
  apply StatMech.Universality.hexEndpointCoordRun_pos_exists_aw ts hlegal

/--
[hexEndpoint_vertex_exists_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_vertex_exists_aw_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  ∃ c : HexAWCoord, hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
-- proof
  apply StatMech.Universality.hexEndpoint_vertex_exists_aw ts hlegal

/--
[hexEndpointCoordRun_pos_eq_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpointCoordRun_pos_eq_aw_eq
  {ts : List ℤ}
  {c : HexAWCoord}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hvertex : hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) :
-- imply
  (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos = hexAWReturnPos c := by
-- proof
  apply StatMech.Universality.hexEndpointCoordRun_pos_eq_aw ts c hlegal hvertex

/--
[hexEndpointCoordRun_dir_color_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpointCoordRun_dir_color_aw_eq
  {ts : List ℤ}
  {c : HexAWCoord}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hvertex : hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) :
-- imply
  match c.color with := by
-- proof
  apply StatMech.Universality.hexEndpointCoordRun_dir_color_aw ts c hlegal hvertex

/--
[hexEndpoint_mid_incident_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_mid_incident_aw_eq
  {ts : List ℤ}
  {c : HexAWCoord}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hvertex : hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) :
-- imply
  ∃ e : Fin 3, hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e := by
-- proof
  apply StatMech.Universality.hexEndpoint_mid_incident_aw ts c hlegal hvertex

/--
[hexEndpoint_forward_vertex_of_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_forward_vertex_of_mid_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {e : Fin 3}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e) :
-- imply
  hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos c ∨ hexInfra_midAccum hexAWStart 1 ts + halfStep (hexInfra_headAccum 1 ts) = hexAWPos (hexAWNeighbor c e) := by
-- proof
  apply StatMech.Universality.hexEndpoint_forward_vertex_of_mid ts c e hlegal hmid

/--
[hexEndpoint_next_mid_of_forward_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_next_mid_of_forward_vertex_eq
  {s : List ℤ}
  {t : ℤ}
  {c : HexAWCoord}
  {e : Fin 3}
-- given
  (hlegal : ∀ u ∈ s, u = 1 ∨ u = -1)
  (ht : t = 1 ∨ t = -1)
  (hmid : hexInfra_midAccum hexAWStart 1 s = hexAWMid c e)
  (hforward : hexInfra_midAccum hexAWStart 1 s + halfStep (hexInfra_headAccum 1 s) = hexAWPos c) :
-- imply
  ∃ f : Fin 3, f ≠ e ∧ hexInfra_midAccum hexAWStart 1 (s ++ [t]) = hexAWMid c f := by
-- proof
  apply StatMech.Universality.hexEndpoint_next_mid_of_forward_vertex s t c e hlegal ht hmid hforward

/--
[hexEndpoint_previous_mid_of_forward_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_previous_mid_of_forward_outer_eq
  {s : List ℤ}
  {t : ℤ}
  {c : HexAWCoord}
  {e : Fin 3}
-- given
  (hlegal : ∀ u ∈ s, u = 1 ∨ u = -1)
  (ht : t = 1 ∨ t = -1)
  (hmid : hexInfra_midAccum hexAWStart 1 (s ++ [t]) = hexAWMid c e)
  (hforward : hexInfra_midAccum hexAWStart 1 (s ++ [t]) + halfStep (hexInfra_headAccum 1 (s ++ [t])) = hexAWPos (hexAWNeighbor c e)) :
-- imply
  ∃ f : Fin 3, f ≠ e ∧ hexInfra_midAccum hexAWStart 1 s = hexAWMid c f := by
-- proof
  apply StatMech.Universality.hexEndpoint_previous_mid_of_forward_outer s t c e hlegal ht hmid hforward

/--
[hexEndpoint_internal_mid_forces_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_internal_mid_forces_second_eq
  {ts : List ℤ}
  {c : HexAWCoord}
  {e : Fin 3}
  {k : ℕ}
-- given
  (hkpos : 0 < k)
  (hklt : k < ts.length)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) = hexAWMid c e) :
-- imply
  ∃ f : Fin 3, f ≠ e ∧ PassesThrough hexAWStart 1 ts (hexAWMid c f) := by
-- proof
  apply StatMech.Universality.hexEndpoint_internal_mid_forces_second ts c e k hkpos hklt hlegal hmid

/--
[hexEndpoint_return_direction_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_return_direction_cases_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hreturn : hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) = m + halfStep h) :
-- imply
  halfStep (hexInfra_headAccum h ts) = halfStep h ∨ halfStep (hexInfra_headAccum h ts) = halfStep (h + 2) ∨ halfStep (hexInfra_headAccum h ts) = halfStep (h + 4) := by
-- proof
  apply StatMech.Universality.hexEndpoint_return_direction_cases m h ts hlegal hreturn

/--
[hexEndpoint_repeated_lookahead_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_repeated_lookahead_direction_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).LegalTurns)
  (hrepeat : hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) ∈ (ofTurns a h0 ts).endpointVertices) :
-- imply
  ∃ k : ℕ, k < ts.length ∧ hexJordan_vertexPos a h0 ts k = hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) ∧ (let hk := hexInfra_headAccum h0 (ts.take k) halfStep (hexInfra_headAccum h0 ts) = halfStep hk ∨ halfStep (hexInfra_headAccum h0 ts) = halfStep (hk + 2) ∨ halfStep (hexInfra_headAccum h0 ts) = halfStep (hk + 4)) := by
-- proof
  apply StatMech.Universality.hexEndpoint_repeated_lookahead_direction a h0 ts hlegal hrepeat

/--
[hexEndpoint_prefix_mid_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_prefix_mid_mem_eq
  {a : ℂ}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (h0 : ℤ)
  (hk : k ≤ ts.length) :
-- imply
  PassesThrough a h0 ts (hexInfra_midAccum a h0 (ts.take k)) := by
-- proof
  apply StatMech.Universality.hexEndpoint_prefix_mid_mem a h0 ts k hk

/--
[hexEndpoint_previous_mid_is_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_previous_mid_is_label_eq
  {v du m : ℂ}
  {j : Fin 3}
-- given
  (h H : ℤ)
  (hm : m + halfStep h = v)
  (hj : labelMid v du j + halfStep H = v)
  (horbit : halfStep H = halfStep h ∨ halfStep H = halfStep (h + 2) ∨ halfStep H = halfStep (h + 4)) :
-- imply
  ∃ l : Fin 3, m = labelMid v du l := by
-- proof
  apply StatMech.Universality.hexEndpoint_previous_mid_is_label v du m j h H hm hj horbit

/--
[hexEndpoint_next_mid_is_distinct_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_next_mid_is_distinct_label_eq
  {v du m : ℂ}
  {j : Fin 3}
-- given
  (h t : ℤ)
  (hm : m = labelMid v du j)
  (hv : m + halfStep h = v)
  (ht : t = 1 ∨ t = -1) :
-- imply
  ∃ l : Fin 3, l ≠ j ∧ m + halfStep h + halfStep (h + t) = labelMid v du l := by
-- proof
  apply StatMech.Universality.hexEndpoint_next_mid_is_distinct_label v du m j h t hm hv ht

/--
[specialMidCount_ge_two_of_labels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma specialMidCount_ge_two_of_labels_eq
  {a : ℂ}
  {v du : ℂ}
  {ts : List ℤ}
  {j l : Fin 3}
-- given
  (h0 : ℤ)
  (hjl : j ≠ l)
  (hj : PassesThrough a h0 ts (labelMid v du j))
  (hl : PassesThrough a h0 ts (labelMid v du l)) :
-- imply
  2 ≤ specialMidCount a h0 v du ts := by
-- proof
  apply StatMech.Universality.specialMidCount_ge_two_of_labels a h0 v du ts j l hjl hj hl

/--
[hexEndpoint_count_ge_two_of_lookahead_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_count_ge_two_of_lookahead_mem_eq
  {a : ℂ}
  {v du : ℂ}
  {j : Fin 3}
  {ts : List ℤ}
  {L : HexCyclicLaunch a h0 v du j ts}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).LegalTurns)
  (hmem : v ∈ (ofTurns a h0 ts).endpointVertices) :
-- imply
  2 ≤ specialMidCount a h0 v du ts := by
-- proof
  apply StatMech.Universality.hexEndpoint_count_ge_two_of_lookahead_mem a h0 v du j ts L hlegal hmem

/--
[hexEndpoint_vertices_eq_append_lookahead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_vertices_eq_append_lookahead_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 ts).vertices = (ofTurns a h0 ts).endpointVertices ++ [hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts)] := by
-- proof
  apply StatMech.Universality.hexEndpoint_vertices_eq_append_lookahead a h0 ts

/--
[hexEndpoint_isSAW_of_lookahead_fresh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_isSAW_of_lookahead_fresh_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 ts).EndpointIsSAW)
  (hfresh : hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) ∉ (ofTurns a h0 ts).endpointVertices) :
-- imply
  (ofTurns a h0 ts).IsSAW := by
-- proof
  apply StatMech.Universality.hexEndpoint_isSAW_of_lookahead_fresh a h0 ts hsaw hfresh

/--
[hexEndpoint_full_legal_of_count_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_full_legal_of_count_one_eq
  {a : ℂ}
  {v du : ℂ}
  {j : Fin 3}
  {ts : List ℤ}
  {L : HexCyclicLaunch a h0 v du j ts}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW)
  (hcount : specialMidCount a h0 v du ts = 1) :
-- imply
  (ofTurns a h0 ts).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexEndpoint_full_legal_of_count_one a h0 v du j ts L hlegal hcount

/--
[HexCyclicLaunch.extension_counts_of_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma extension_counts_of_one_eq
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {j : Fin 3}
  {ts : List ℤ}
  {L : HexCyclicLaunch a h0 v du j ts}
-- given
  (hdu : du ≠ 0)
  (hcount : specialMidCount a h0 v du ts = 1) :
-- imply
  specialMidCount a h0 v du (ts ++ [-1]) = 2 ∧ specialMidCount a h0 v du (ts ++ [1]) = 2 := by
-- proof
  apply StatMech.Universality.HexCyclicLaunch.extension_counts_of_one L hdu hcount

/--
[hexEndpoint_erase_last_launch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_erase_last_launch_eq
  {a : ℂ}
  {v du : ℂ}
  {j : Fin 3}
  {base : List ℤ}
  {t : ℤ}
-- given
  (h0 : ℤ)
  (ht : t = 1 ∨ t = -1)
  (hlast : hexInfra_midAccum a h0 base + halfStep (hexInfra_headAccum h0 base) = v)
  (hend : (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du j)) :
-- imply
  ∃ l : Fin 3, l ≠ j ∧ HexCyclicLaunch a h0 v du l base := by
-- proof
  apply StatMech.Universality.hexEndpoint_erase_last_launch a h0 v du j base t ht hlast hend

/--
[hexEndpoint_base_count_one_of_extension_count_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_base_count_one_of_extension_count_two_eq
  {a : ℂ}
  {v du : ℂ}
  {j : Fin 3}
  {base : List ℤ}
  {t : ℤ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0)
  (hend : (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du j))
  (hnew : ¬ PassesThrough a h0 base (labelMid v du j))
  (hcount : specialMidCount a h0 v du (base ++ [t]) = 2) :
-- imply
  specialMidCount a h0 v du base = 1 := by
-- proof
  apply StatMech.Universality.hexEndpoint_base_count_one_of_extension_count_two a h0 v du j base t hdu hend hnew hcount

/--
[endpointParafSummand_eq_zero_of_not_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointParafSummand_eq_zero_of_not_endsAt_eq
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hne : ¬(ofTurns a h0 ts).EndsAt z) :
-- imply
  endpointParafSummand region a h0 z σ x ts = 0 := by
-- proof
  apply StatMech.Universality.endpointParafSummand_eq_zero_of_not_endsAt region a h0 z σ x ts hne

/--
[endpointCombinedSummand_at_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointCombinedSummand_at_p_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hend : (ofTurns a h0 ts).EndsAt (v + du)) :
-- imply
  endpointCombinedSummand region a h0 v du ts = ((v + du) - v) * endpointParafSummand region a h0 (v + du) (5 / 8) hexChi ts := by
-- proof
  apply StatMech.Universality.endpointCombinedSummand_at_p hdu hend

/--
[endpointCombinedSummand_at_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointCombinedSummand_at_q_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega * du)) :
-- imply
  endpointCombinedSummand region a h0 v du ts = ((v + hexOmega * du) - v) * endpointParafSummand region a h0 (v + hexOmega * du) (5 / 8) hexChi ts := by
-- proof
  apply StatMech.Universality.endpointCombinedSummand_at_q hdu hend

/--
[endpointCombinedSummand_at_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointCombinedSummand_at_r_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du)) :
-- imply
  endpointCombinedSummand region a h0 v du ts = ((v + hexOmega ^ 2 * du) - v) * endpointParafSummand region a h0 (v + hexOmega ^ 2 * du) (5 / 8) hexChi ts := by
-- proof
  apply StatMech.Universality.endpointCombinedSummand_at_r hdu hend

/--
[endpointParafSummand_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointParafSummand_nil_eq
  {a : ℂ}
  {σ x : ℝ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (ha : region a) :
-- imply
  endpointParafSummand region a h0 a σ x [] = 1 := by
-- proof
  apply StatMech.Universality.endpointParafSummand_nil region a h0 σ x ha

/--
[endpointContribution_eq_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointContribution_eq_summand_eq
  {a : ℂ}
  {z v : ℂ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hcond : (ofTurns a h0 ts).EndpointIsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt z) :
-- imply
  (z - v) * endpointParafSummand region a h0 z (5 / 8) hexChi ts = hexContribution (z - v) (ofTurns a h0 ts).turnCount (ofTurns a h0 ts).endpointNumVertices := by
-- proof
  apply StatMech.Universality.endpointContribution_eq_summand region a h0 z v ts hcond

/--
[endpointParafSummand_guard_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointParafSummand_guard_of_ne_eq
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hne : endpointParafSummand region a h0 z σ x ts ≠ 0) :
-- imply
  (ofTurns a h0 ts).EndpointIsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt z := by
-- proof
  apply StatMech.Universality.endpointParafSummand_guard_of_ne region a h0 z σ x ts hne

/--
[endpointLength_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointLength_le_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 ts).EndpointIsSAW)
  (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
-- imply
  ts.length ≤ R.verts.card := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointLength_le R a h0 ts hsaw hstay

/--
[endpointParaf_support_subset_boundedLegal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointParaf_support_subset_boundedLegal_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  Function.support (endpointParafSummand R.inRegion a h0 z σ x) ⊆ {ts : List ℤ | (∀ t ∈ ts, t = 1 ∨ t = -1) ∧ ts.length ≤ R.verts.card} := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointParaf_support_subset_boundedLegal R a h0 z σ x

/--
[endpointParaf_support_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointParaf_support_finite_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  (Function.support (endpointParafSummand R.inRegion a h0 z σ x)).Finite := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointParaf_support_finite R a h0 z σ x

/--
[endpointParaf_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointParaf_summable_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  Summable (endpointParafSummand R.inRegion a h0 z σ x) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointParaf_summable R a h0 z σ x

/--
[endpointCombined_support_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointCombined_support_valid_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hne : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
-- imply
  (ofTurns a h0 ts).EndpointIsLegalSAW ∧ (ofTurns a h0 ts).StaysIn R.inRegion := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointCombined_support_valid R a h0 v du ts hne

/--
[endpointCombined_support_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointCombined_support_endsAt_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hne : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
-- imply
  (ofTurns a h0 ts).EndsAt (v + du) ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega * du) ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointCombined_support_endsAt R a h0 v du ts hne

/--
[endpointCombined_support_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointCombined_support_finite_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (Function.support (endpointCombinedSummand R.inRegion a h0 v du)).Finite := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointCombined_support_finite R a h0 v du

/--
[mem_endpointCombinedSupportFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma mem_endpointCombinedSupportFinset_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  ts ∈ R.endpointCombinedSupportFinset a h0 v du ↔ endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0 := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.mem_endpointCombinedSupportFinset R a h0 v du ts

/--
[endpointCombined_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointCombined_summable_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Summable (endpointCombinedSummand R.inRegion a h0 v du) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointCombined_summable R a h0 v du

/--
[mem_endpointVisitClassFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma mem_endpointVisitClassFinset_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {k : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  ts ∈ R.endpointVisitClassFinset a h0 v du k ↔ endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0 ∧ specialMidCount a h0 v du ts = k := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.mem_endpointVisitClassFinset R a h0 v du k ts

/--
[endpointSupport_specialMidCount_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointSupport_specialMidCount_pos_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hts : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
-- imply
  0 < specialMidCount a h0 v du ts := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointSupport_specialMidCount_pos R a h0 v du ts hts

/--
[endpointSupport_specialMidCount_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointSupport_specialMidCount_cases_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hts : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
-- imply
  specialMidCount a h0 v du ts = 1 ∨ specialMidCount a h0 v du ts = 2 ∨ specialMidCount a h0 v du ts = 3 := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointSupport_specialMidCount_cases R a h0 v du ts hts

/--
[endpointSupportFinset_eq_visitClasses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointSupportFinset_eq_visitClasses_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  R.endpointCombinedSupportFinset a h0 v du = R.endpointVisitClassFinset a h0 v du 1 ∪ R.endpointVisitClassFinset a h0 v du 2 ∪ R.endpointVisitClassFinset a h0 v du 3 := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointSupportFinset_eq_visitClasses R a h0 v du

/--
[endpointVisitClassFinset_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointVisitClassFinset_disjoint_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
  {k l : ℕ}
-- given
  (h0 : ℤ)
  (hkl : k ≠ l) :
-- imply
  Disjoint (R.endpointVisitClassFinset a h0 v du k) (R.endpointVisitClassFinset a h0 v du l) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.endpointVisitClassFinset_disjoint R a h0 v du hkl

/--
[endpointVertexSum_eq_tsum_combined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointVertexSum_eq_tsum_combined_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  ((v + du) - v) * endpointParafObservable R.inRegion a h0 (v + du) (5 / 8) hexChi + ((v + hexOmega * du) - v) * endpointParafObservable R.inRegion a h0 (v + hexOmega * du) (5 / 8) hexChi + ((v + hexOmega ^ 2 * du) - v) * endpointParafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5 / 8) hexChi = ∑' ts, endpointCombinedSummand R.inRegion a h0 v du ts := by
-- proof
  apply StatMech.Universality.endpointVertexSum_eq_tsum_combined R a h0 v du

/--
[endpointNumVertices_append_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointNumVertices_append_one_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 t : ℤ) :
-- imply
  (ofTurns a h0 (ts ++ [t])).endpointNumVertices = (ofTurns a h0 ts).endpointNumVertices + 1 := by
-- proof
  apply StatMech.Universality.endpointNumVertices_append_one a h0 t ts

/--
[endpoint_genuine_triplet_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpoint_genuine_triplet_zero_eq
  {a : ℂ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hp : (ofTurns a h0 ts).EndpointIsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region ∧ (ofTurns a h0 ts).EndsAt (v + du))
  (hq : (ofTurns a h0 (ts ++ [-1])).EndpointIsLegalSAW ∧ (ofTurns a h0 (ts ++ [-1])).StaysIn region ∧ (ofTurns a h0 (ts ++ [-1])).EndsAt (v + hexOmega * du))
  (hr : (ofTurns a h0 (ts ++ [1])).EndpointIsLegalSAW ∧ (ofTurns a h0 (ts ++ [1])).StaysIn region ∧ (ofTurns a h0 (ts ++ [1])).EndsAt (v + hexOmega ^ 2 * du)) :
-- imply
  ((v + du) - v) * endpointParafSummand region a h0 (v + du) (5 / 8) hexChi ts + ((v + hexOmega * du) - v) * endpointParafSummand region a h0 (v + hexOmega * du) (5 / 8) hexChi (ts ++ [-1]) + ((v + hexOmega ^ 2 * du) - v) * endpointParafSummand region a h0 (v + hexOmega ^ 2 * du) (5 / 8) hexChi (ts ++ [1]) = 0 := by
-- proof
  apply StatMech.Universality.endpoint_genuine_triplet_zero region a h0 v du ts hp hq hr

/--
[endpoint_genuine_pair_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpoint_genuine_pair_zero_eq
  {a : ℂ}
  {v du : ℂ}
  {base Lq Lr : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hLqsum : Lq.sum = -4)
  (hLrsum : Lr.sum = 4)
  (hlen : Lq.length = Lr.length)
  (hq : (ofTurns a h0 (base ++ Lq)).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ Lq)).StaysIn region ∧ (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
  (hr : (ofTurns a h0 (base ++ Lr)).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ Lr)).StaysIn region ∧ (ofTurns a h0 (base ++ Lr)).EndsAt (v + hexOmega ^ 2 * du)) :
-- imply
  ((v + hexOmega * du) - v) * endpointParafSummand region a h0 (v + hexOmega * du) (5 / 8) hexChi (base ++ Lq) + ((v + hexOmega ^ 2 * du) - v) * endpointParafSummand region a h0 (v + hexOmega ^ 2 * du) (5 / 8) hexChi (base ++ Lr) = 0 := by
-- proof
  apply StatMech.Universality.endpoint_genuine_pair_zero region a h0 v du base Lq Lr hLqsum hLrsum hlen hq hr

/--
[endpoint_genuine_pair_zero_via_reversal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpoint_genuine_pair_zero_via_reversal_eq
  {a : ℂ}
  {v du : ℂ}
  {base Lq : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hLqsum : Lq.sum = -4)
  (hq : (ofTurns a h0 (base ++ Lq)).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ Lq)).StaysIn region ∧ (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
  (hr : (ofTurns a h0 (base ++ loopReverse Lq)).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ loopReverse Lq)).StaysIn region ∧ (ofTurns a h0 (base ++ loopReverse Lq)).EndsAt (v + hexOmega ^ 2 * du)) :
-- imply
  ((v + hexOmega * du) - v) * endpointParafSummand region a h0 (v + hexOmega * du) (5 / 8) hexChi (base ++ Lq) + ((v + hexOmega ^ 2 * du) - v) * endpointParafSummand region a h0 (v + hexOmega ^ 2 * du) (5 / 8) hexChi (base ++ loopReverse Lq) = 0 := by
-- proof
  apply StatMech.Universality.endpoint_genuine_pair_zero_via_reversal region a h0 v du base Lq hLqsum hq hr

/--
[anchoredLoopReverse_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma anchoredLoopReverse_nil_eq :
-- imply
  anchoredLoopReverse [] = [] := by
-- proof
  apply StatMech.Universality.anchoredLoopReverse_nil

/--
[anchoredLoopReverse_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma anchoredLoopReverse_cons_eq
  {t : ℤ}
  {ts : List ℤ} :
-- imply
  anchoredLoopReverse (t :: ts) = (-t) :: loopReverse ts := by
-- proof
  apply StatMech.Universality.anchoredLoopReverse_cons t ts

/--
[anchoredLoopReverse_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma anchoredLoopReverse_sum_eq
  {L : List ℤ} :
-- imply
  (anchoredLoopReverse L).sum = -L.sum := by
-- proof
  apply StatMech.Universality.anchoredLoopReverse_sum L

/--
[anchoredLoopReverse_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma anchoredLoopReverse_length_eq
  {L : List ℤ} :
-- imply
  (anchoredLoopReverse L).length = L.length := by
-- proof
  apply StatMech.Universality.anchoredLoopReverse_length L

/--
[anchoredLoopReverse_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma anchoredLoopReverse_legal_eq
  {L : List ℤ}
-- given
  (hL : ∀ t ∈ L, t = 1 ∨ t = -1) :
-- imply
  ∀ t ∈ anchoredLoopReverse L, t = 1 ∨ t = -1 := by
-- proof
  apply StatMech.Universality.anchoredLoopReverse_legal L hL

/--
[anchoredLoopReverse_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma anchoredLoopReverse_involutive_eq
  {L : List ℤ} :
-- imply
  anchoredLoopReverse (anchoredLoopReverse L) = L := by
-- proof
  apply StatMech.Universality.anchoredLoopReverse_involutive L

/--
[hexEndpoint_midsAux_loopReverse_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_midsAux_loopReverse_exact_eq
  {m : ℂ}
  {L : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ L, t = 1 ∨ t = -1) :
-- imply
  midsAux (hexInfra_midAccum m h L) (hexInfra_headAccum h L + 3) (loopReverse L) = (midsAux m h L).reverse := by
-- proof
  apply StatMech.Universality.hexEndpoint_midsAux_loopReverse_exact m h L hlegal

/--
[hexEndpoint_verticesAux_loopReverse_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_verticesAux_loopReverse_exact_eq
  {m : ℂ}
  {L : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ L, t = 1 ∨ t = -1) :
-- imply
  verticesAux (hexInfra_midAccum m h L) (hexInfra_headAccum h L + 3) (loopReverse L) = (verticesAux m h L).dropLast.reverse ++ [m - halfStep h] := by
-- proof
  apply StatMech.Universality.hexEndpoint_verticesAux_loopReverse_exact m h L hlegal

/--
[hexEndpoint_midsAux_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_midsAux_append_eq
  {m : ℂ}
  {xs ys : List ℤ}
-- given
  (h : ℤ) :
-- imply
  midsAux m h (xs ++ ys) = (midsAux m h xs).dropLast ++ midsAux (hexInfra_midAccum m h xs) (hexInfra_headAccum h xs) ys := by
-- proof
  apply StatMech.Universality.hexEndpoint_midsAux_append m h xs ys

/--
[hexEndpoint_verticesAux_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_verticesAux_append_eq
  {m : ℂ}
  {xs ys : List ℤ}
-- given
  (h : ℤ) :
-- imply
  verticesAux m h (xs ++ ys) = (verticesAux m h xs).dropLast ++ verticesAux (hexInfra_midAccum m h xs) (hexInfra_headAccum h xs) ys := by
-- proof
  apply StatMech.Universality.hexEndpoint_verticesAux_append m h xs ys

/--
[hexEndpoint_dropLast_verticesAux_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_dropLast_verticesAux_append_eq
  {m : ℂ}
  {xs ys : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (verticesAux m h (xs ++ ys)).dropLast = (verticesAux m h xs).dropLast ++ (verticesAux (hexInfra_midAccum m h xs) (hexInfra_headAccum h xs) ys).dropLast := by
-- proof
  apply StatMech.Universality.hexEndpoint_dropLast_verticesAux_append m h xs ys

/--
[anchoredLoopReverse_midsAux_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma anchoredLoopReverse_midsAux_eq_eq
  {m : ℂ}
  {tail : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
  (hsum : ((1 : ℤ) :: tail).sum = -4)
  (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) + halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) = m + halfStep h) :
-- imply
  midsAux m h (anchoredLoopReverse ((1 : ℤ) :: tail)) = m :: (midsAux m h ((1 : ℤ) :: tail)).tail.reverse := by
-- proof
  apply StatMech.Universality.anchoredLoopReverse_midsAux_eq m h tail hlegal hsum hclose

/--
[anchoredLoopReverse_midAccum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma anchoredLoopReverse_midAccum_eq_eq
  {m : ℂ}
  {tail : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
  (hsum : ((1 : ℤ) :: tail).sum = -4)
  (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) + halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) = m + halfStep h) :
-- imply
  hexInfra_midAccum m h (anchoredLoopReverse ((1 : ℤ) :: tail)) = m + halfStep h + halfStep (h + 1) := by
-- proof
  apply StatMech.Universality.anchoredLoopReverse_midAccum_eq m h tail hlegal hsum hclose

/--
[anchoredLoopReverse_verticesAux_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma anchoredLoopReverse_verticesAux_eq_eq
  {m : ℂ}
  {tail : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
  (hsum : ((1 : ℤ) :: tail).sum = -4)
  (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) + halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) = m + halfStep h) :
-- imply
  verticesAux m h (anchoredLoopReverse ((1 : ℤ) :: tail)) = (m + halfStep h) :: (verticesAux m h ((1 : ℤ) :: tail)).dropLast.tail.reverse ++ [m + halfStep h] := by
-- proof
  apply StatMech.Universality.anchoredLoopReverse_verticesAux_eq m h tail hlegal hsum hclose

/--
[anchoredLoopReverse_endpointVertices_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma anchoredLoopReverse_endpointVertices_eq_eq
  {m : ℂ}
  {tail : List ℤ}
-- given
  (h : ℤ)
  (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
  (hsum : ((1 : ℤ) :: tail).sum = -4)
  (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) + halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) = m + halfStep h) :
-- imply
  (verticesAux m h (anchoredLoopReverse ((1 : ℤ) :: tail))).dropLast = (m + halfStep h) :: (verticesAux m h ((1 : ℤ) :: tail)).dropLast.tail.reverse := by
-- proof
  apply StatMech.Universality.anchoredLoopReverse_endpointVertices_eq m h tail hlegal hsum hclose

/--
[endpoint_genuine_pair_zero_via_anchored_reversal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpoint_genuine_pair_zero_via_anchored_reversal_eq
  {a : ℂ}
  {v du : ℂ}
  {base Lq : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hLqsum : Lq.sum = -4)
  (hq : (ofTurns a h0 (base ++ Lq)).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ Lq)).StaysIn region ∧ (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
  (hr : (ofTurns a h0 (base ++ anchoredLoopReverse Lq)).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ anchoredLoopReverse Lq)).StaysIn region ∧ (ofTurns a h0 (base ++ anchoredLoopReverse Lq)).EndsAt (v + hexOmega ^ 2 * du)) :
-- imply
  ((v + hexOmega * du) - v) * endpointParafSummand region a h0 (v + hexOmega * du) (5 / 8) hexChi (base ++ Lq) + ((v + hexOmega ^ 2 * du) - v) * endpointParafSummand region a h0 (v + hexOmega ^ 2 * du) (5 / 8) hexChi (base ++ anchoredLoopReverse Lq) = 0 := by
-- proof
  apply StatMech.Universality.endpoint_genuine_pair_zero_via_anchored_reversal region a h0 v du base Lq hLqsum hq hr

/--
[HexEndpointCyclicTriplet.contribution_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma contribution_zero_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexEndpointCyclicTriplet region a h0 v du} :
-- imply
  (labelMid v du C.baseLabel - v) * endpointParafSummand region a h0 (labelMid v du C.baseLabel) (5 / 8) hexChi C.base + (labelMid v du (hexCyclicSucc C.baseLabel) - v) * endpointParafSummand region a h0 (labelMid v du (hexCyclicSucc C.baseLabel)) (5 / 8) hexChi (C.base ++ [-1]) + (labelMid v du (hexCyclicPred C.baseLabel) - v) * endpointParafSummand region a h0 (labelMid v du (hexCyclicPred C.baseLabel)) (5 / 8) hexChi (C.base ++ [1]) = 0 := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicTriplet.contribution_zero C

/--
[endpointCombinedSummand_at_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma endpointCombinedSummand_at_label_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {j : Fin 3}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (hend : (ofTurns a h0 ts).EndsAt (labelMid v du j)) :
-- imply
  endpointCombinedSummand region a h0 v du ts = (labelMid v du j - v) * endpointParafSummand region a h0 (labelMid v du j) (5 / 8) hexChi ts := by
-- proof
  apply StatMech.Universality.endpointCombinedSummand_at_label hdu j hend

/--
[hexEndpoint_kTwo_mem_cyclicTriplet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma hexEndpoint_kTwo_mem_cyclicTriplet_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {j : Fin 3}
  {base : List ℤ}
  {t : ℤ}
-- given
  (hdu : du ≠ 0)
  (hvalid : (ofTurns a h0 (base ++ [t])).EndpointIsLegalSAW ∧ (ofTurns a h0 (base ++ [t])).StaysIn region ∧ (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du j))
  (hcount : specialMidCount a h0 v du (base ++ [t]) = 2)
  (hlast : hexInfra_midAccum a h0 base + halfStep (hexInfra_headAccum h0 base) = v)
  (hnew : ¬ PassesThrough a h0 base (labelMid v du j))
  (hall : ∀ l : Fin 3, region (labelMid v du l)) :
-- imply
  ∃ C : HexEndpointCyclicTriplet region a h0 v du, base ++ [t] ∈ C.piece ∧ C.base = base := by
-- proof
  apply StatMech.Universality.hexEndpoint_kTwo_mem_cyclicTriplet j base t hdu hvalid hcount hlast hnew hall

/--
[HexEndpointCyclicTriplet.sum_piece_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma sum_piece_zero_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {C : HexEndpointCyclicTriplet region a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  ∑ ts ∈ C.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
-- proof
  apply StatMech.Universality.HexEndpointCyclicTriplet.sum_piece_zero hdu C

/--
[HexEndpointLoopGeometry.reversed_legalTurns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma reversed_legalTurns_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {G : HexEndpointLoopGeometry region a h0 v du} :
-- imply
  (ofTurns a h0 (G.base ++ anchoredLoopReverse G.loopQ)).LegalTurns := by
-- proof
  apply StatMech.Universality.HexEndpointLoopGeometry.reversed_legalTurns G

/--
[HexEndpointLoopPair.sum_piece_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma sum_piece_zero_eq_2
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {P : HexEndpointLoopPair region a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  ∑ ts ∈ P.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
-- proof
  apply StatMech.Universality.HexEndpointLoopPair.sum_piece_zero hdu P

/--
[HexEndpointLocalAtom.sum_piece_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma sum_piece_zero_eq_3
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {A : HexEndpointLocalAtom region a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  ∑ ts ∈ A.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
-- proof
  apply StatMech.Universality.HexEndpointLocalAtom.sum_piece_zero hdu A

/--
[HexEndpointLocalPartition.vertex_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean)
-/
@[path]
private lemma vertex_relation_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {P : HexEndpointLocalPartition R a h0 v du}
-- given
  (hdu : du ≠ 0) :
-- imply
  ((v + du) - v) * endpointParafObservable R.inRegion a h0 (v + du) (5 / 8) hexChi + ((v + hexOmega * du) - v) * endpointParafObservable R.inRegion a h0 (v + hexOmega * du) (5 / 8) hexChi + ((v + hexOmega ^ 2 * du) - v) * endpointParafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5 / 8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.HexEndpointLocalPartition.vertex_relation hdu P


-- created on 2026-10-23
