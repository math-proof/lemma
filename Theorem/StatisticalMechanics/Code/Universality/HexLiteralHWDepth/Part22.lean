/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part20


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_intervalTopCoord_white (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (hlhd_intervalTopCoord ts hleg hhalf p hp).color = .white := by
  let far := hlhd_intervalFarCoord ts hleg hhalf p hp
  change (if far.color = .white then far else hexAWNeighbor far 0).color = .white
  by_cases hc : far.color = .white
  · simp [hc]
  · rw [if_neg hc]
    rcases far with ⟨i, j, color⟩
    cases color <;> simp_all [hexAWNeighbor]

theorem hlhd_neighbor_zero_depth (c : HexAWCoord) :
    hexAWDepth (hexAWNeighbor c 0) = hexAWDepth c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> simp [hexAWNeighbor, hexAWDepth, hexAWLong]

theorem hlhd_intervalTopCoord_depth (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWDepth (hlhd_intervalTopCoord ts hleg hhalf p hp) =
      hlhd_width ts hleg p := by
  let far := hlhd_intervalFarCoord ts hleg hhalf p hp
  by_cases hc : far.color = .white
  · simpa [hlhd_intervalTopCoord, far, hc] using
      hlhd_intervalFarCoord_depth ts hleg hhalf p hp
  · rw [hlhd_intervalTopCoord, show
        hlhd_intervalFarCoord ts hleg hhalf p hp = far from rfl, if_neg hc,
      hlhd_neighbor_zero_depth]
    exact hlhd_intervalFarCoord_depth ts hleg hhalf p hp

theorem hlhd_intervalExits_false_of_far_black (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (hblack : (hlhd_intervalFarCoord ts hleg hhalf p hp).color = .black) :
    hlhd_intervalExits ts hleg hhalf p hp = false := by
  unfold hlhd_intervalExits
  rw [hlhd_intervalLastEdge_zero_of_far_black ts hleg hhalf p hp hblack]
  decide

theorem hlhd_intervalFarCoord_white_of_exits (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (hexits : hlhd_intervalExits ts hleg hhalf p hp = true) :
    (hlhd_intervalFarCoord ts hleg hhalf p hp).color = .white := by
  cases hc : (hlhd_intervalFarCoord ts hleg hhalf p hp).color with
  | white => rfl
  | black =>
      have hf := hlhd_intervalExits_false_of_far_black
        ts hleg hhalf p hp hc
      rw [hexits] at hf
      contradiction

theorem hlhd_hexUnit_add_eq_of_eq (h k t : ℤ)
    (hu : hexUnit h = hexUnit k) :
    hexUnit (h + t) = hexUnit (k + t) := by
  rw [hhe_hexUnit_add, hhe_hexUnit_add, hu]


theorem hlhd_exit_heading_unit (c d : HexAWCoord) (e : Fin 3)
    (he : hexAWNeighbor c e = d) (hd : d.color = .white)
    (hin : e = 1 ∨ e = 2) :
    hexUnit (hexAWHeading c e + hlhd_exitTurn e) =
      hexUnit (hexAWHeading d 0) := by
  rcases c with ⟨i, j, color⟩
  rcases d with ⟨i', j', color'⟩
  rcases hin with rfl | rfl <;>
    cases color <;> cases color' <;>
    simp [hexAWNeighbor, hexAWHeading, hlhd_exitTurn] at he hd ⊢
  all_goals
    rw [show (7 : ℤ) = 1 + 6 by norm_num, hexUnit_add_six]


theorem hlhd_append_exit_endsAt (ws : List ℤ)
    (c d : HexAWCoord) (e : Fin 3)
    (hend : (ofTurns hexAWStart 1 ws).EndsAt (hexAWMid c e))
    (hhead : hexUnit (hexInfra_headAccum 1 ws) =
      hexUnit (hexAWHeading c e))
    (he : hexAWNeighbor c e = d) (hd : d.color = .white)
    (hin : e = 1 ∨ e = 2) :
    (ofTurns hexAWStart 1 (ws ++ [hlhd_exitTurn e])).EndsAt
      (hexAWMid d 0) := by
  have hhead' := hlhd_hexUnit_add_eq_of_eq
    (hexInfra_headAccum 1 ws) (hexAWHeading c e)
    (hlhd_exitTurn e) hhead
  have hexit := hlhd_exit_heading_unit c d e he hd hin
  have hfirst : halfStep (hexInfra_headAccum 1 ws) =
      halfStep (hexAWHeading c e) := by
    unfold halfStep
    rw [hhead]
  have hsecond :
      halfStep (hexInfra_headAccum 1 ws + hlhd_exitTurn e) =
        halfStep (hexAWHeading d 0) := by
    unfold halfStep
    rw [hhead', hexit]
  have htoFar : hexAWMid c e + halfStep (hexAWHeading c e) =
      hexAWPos d := by
    have hstep := hexAWNeighborPos_eq_mid_add c e
    rw [he] at hstep
    exact hstep.symm
  have htoTop : hexAWPos d + halfStep (hexAWHeading d 0) =
      hexAWMid d 0 := by
    have hstep := hexAWMid_sub_pos_eq_halfStep d 0
    rw [← hstep]
    ring
  unfold HexWalk.EndsAt at hend ⊢
  rw [hexInfra_endMid_eq_midAccum] at hend ⊢
  rw [hexCyclic_midAccum_append_single, hend, hfirst, hsecond]
  linear_combination htoFar + htoTop

theorem hlhd_intervalCore_finalCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    let core := hlhd_intervalCore ts hleg hhalf p hp
    let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
    hlhc_prefixCoord core hcore.1 core.length =
      hlhd_intervalFarCoord ts hleg hhalf p hp := by
  dsimp only
  let core := hlhd_intervalCore ts hleg hhalf p hp
  have hcorelen : core.length = (hlhd_intervalRaw ts p).length :=
    hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
      (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hnval := hlhd_intervalRaw_length ts hleg hhalf p hp
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp core.length (by
    rw [hcorelen])]
  unfold hlhd_intervalFarCoord
  congr 2
  omega

theorem hlhd_intervalCore_prevCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    let core := hlhd_intervalCore ts hleg hhalf p hp
    let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
    hlhc_prefixCoord core hcore.1 (core.length - 1) =
      hlhd_intervalPrevCoord ts hleg hhalf p hp := by
  dsimp only
  let core := hlhd_intervalCore ts hleg hhalf p hp
  have hcorelen : core.length = (hlhd_intervalRaw ts p).length :=
    hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
      (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hnval := hlhd_intervalRaw_length ts hleg hhalf p hp
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp
    (core.length - 1) (by rw [hcorelen]; omega)]
  unfold hlhd_intervalPrevCoord
  congr 2
  omega

theorem hlhd_intervalCore_heading_unit (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexUnit (hexInfra_headAccum 1
        (hlhd_intervalCore ts hleg hhalf p hp)) =
      hexUnit (hexAWHeading
        (hlhd_intervalPrevCoord ts hleg hhalf p hp)
        (hlhd_intervalLastEdge ts hleg hhalf p hp)) := by
  let core := hlhd_intervalCore ts hleg hhalf p hp
  let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
  have hne : core ≠ [] := by
    dsimp [core, hlhd_intervalCore, hlhd_coreTurns]
    simp
  have hk : core.length - 1 < core.length := by
    exact Nat.sub_lt (List.length_pos_iff.mpr hne) (by omega)
  have hu := hlhd_prefix_edge_unit core hcore
    (core.length - 1) hk
    (hlhd_intervalLastEdge ts hleg hhalf p hp)
    (hlhd_intervalCore_lastEdge ts hleg hhalf p hp)
  have hsucc : core.length - 1 + 1 = core.length := by omega
  rw [hsucc, List.take_length,
    hlhd_intervalCore_prevCoord ts hleg hhalf p hp] at hu
  exact hu

theorem hlhd_fin3_inward_of_ne_zero (e : Fin 3) (he : e ≠ 0) :
    e = 1 ∨ e = 2 := by
  fin_cases e <;> simp_all

theorem hlhd_fin3_zero_of_decide_ne_false (e : Fin 3)
    (he : decide (e ≠ 0) = false) : e = 0 := by
  by_contra hne
  simp [hne] at he

theorem hlhd_intervalCore_endsAt_top_of_noExit (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (hexits : hlhd_intervalExits ts hleg hhalf p hp = false) :
    (ofTurns hexAWStart 1
      (hlhd_intervalCore ts hleg hhalf p hp)).EndsAt
        (hexAWMid (hlhd_intervalTopCoord ts hleg hhalf p hp) 0) := by
  let prev := hlhd_intervalPrevCoord ts hleg hhalf p hp
  let far := hlhd_intervalFarCoord ts hleg hhalf p hp
  let e := hlhd_intervalLastEdge ts hleg hhalf p hp
  have he0 : e = 0 := by
    apply hlhd_fin3_zero_of_decide_ne_false
    simpa only [e, hlhd_intervalExits] using hexits
  have hfar : hexAWNeighbor prev 0 = far := by
    simpa only [prev, far, e, he0] using
      hlhd_intervalLastEdge_normalized ts hleg hhalf p hp
  have hend := hlhd_intervalCore_endsAt ts hleg hhalf p hp
  have hmid : hexAWMid prev e =
      hexAWMid (hlhd_intervalTopCoord ts hleg hhalf p hp) 0 := by
    rw [he0]
    by_cases hc : far.color = .white
    · rw [hlhd_intervalTopCoord, show
          hlhd_intervalFarCoord ts hleg hhalf p hp = far from rfl,
        if_pos hc, ← hfar]
      exact (hexAWMid_neighbor prev 0).symm
    · rw [hlhd_intervalTopCoord, show
          hlhd_intervalFarCoord ts hleg hhalf p hp = far from rfl,
        if_neg hc, ← hfar, hexAWNeighbor_invol]
  simpa only [prev, e, hmid] using hend


theorem hlhd_intervalEndpoint_endsAt (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (ofTurns hexAWStart 1
      (hlhd_intervalEndpoint ts hleg hhalf p hp)).EndsAt
        (hexAWMid (hlhd_intervalTopCoord ts hleg hhalf p hp) 0) := by
  cases hexits : hlhd_intervalExits ts hleg hhalf p hp with
  | false =>
      simpa [hlhd_intervalEndpoint, hlhd_endpointTurns, hexits] using
        hlhd_intervalCore_endsAt_top_of_noExit
          ts hleg hhalf p hp hexits
  | true =>
      let core := hlhd_intervalCore ts hleg hhalf p hp
      let prev := hlhd_intervalPrevCoord ts hleg hhalf p hp
      let far := hlhd_intervalFarCoord ts hleg hhalf p hp
      let e := hlhd_intervalLastEdge ts hleg hhalf p hp
      have hwhite : far.color = .white := by
        exact hlhd_intervalFarCoord_white_of_exits
          ts hleg hhalf p hp hexits
      have hene : e ≠ 0 := by
        intro he0
        unfold hlhd_intervalExits at hexits
        simp [e, he0] at hexits
      have hin : e = 1 ∨ e = 2 :=
        hlhd_fin3_inward_of_ne_zero e hene
      have hend := hlhd_append_exit_endsAt core prev far e
        (hlhd_intervalCore_endsAt ts hleg hhalf p hp)
        (hlhd_intervalCore_heading_unit ts hleg hhalf p hp)
        (hlhd_intervalLastEdge_normalized ts hleg hhalf p hp)
        hwhite hin
      have htop : hlhd_intervalTopCoord ts hleg hhalf p hp = far := by
        simp [hlhd_intervalTopCoord, far, hwhite]
      simpa [hlhd_intervalEndpoint, hlhd_endpointTurns, hexits,
        core, e, htop] using hend

theorem hlhd_intervalCore_depth_bounds (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (r : ℕ)
    (hr : r ≤ (hlhd_intervalCore ts hleg hhalf p hp).length) :
    0 ≤ hexAWDepth (hlhc_prefixCoord
        (hlhd_intervalCore ts hleg hhalf p hp)
        (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r) ∧
      hexAWDepth (hlhc_prefixCoord
        (hlhd_intervalCore ts hleg hhalf p hp)
        (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r) ≤
        (hlhd_width ts hleg p : ℤ) := by
  have hraw : (hlhd_intervalRaw ts p).length = p.2 - p.1 :=
    hlhd_intervalRaw_length ts hleg hhalf p hp
  have hbounds := hlhd_interval_index_bounds ts hleg hhalf p hp
  rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp r (by
    simpa only [hlhd_intervalCore_length] using hr)]
  apply hlhd_normalized_depth_bounds ts hleg p
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
  · omega
  · rw [hlhd_intervalCore_length, hraw] at hr
    omega

theorem hlhd_intervalCore_white_depth_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (r : ℕ)
    (hr : r ≤ (hlhd_intervalCore ts hleg hhalf p hp).length)
    (hwhite : (hlhc_prefixCoord
      (hlhd_intervalCore ts hleg hhalf p hp)
      (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r).color =
        .white) :
    0 < hexAWDepth (hlhc_prefixCoord
      (hlhd_intervalCore ts hleg hhalf p hp)
      (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r) := by
  have hraw : (hlhd_intervalRaw ts p).length = p.2 - p.1 :=
    hlhd_intervalRaw_length ts hleg hhalf p hp
  have hbounds := hlhd_interval_index_bounds ts hleg hhalf p hp
  by_cases hr0 : r = 0
  · subst r
    have hsource := hlhd_intervalCore_prefixCoord
      ts hleg hhalf p hp 0 (by omega)
    simp only [Nat.add_zero] at hsource
    rw [hlhd_interval_source_normalizes ts hleg hhalf p hp] at hsource
    rw [hsource] at hwhite
    simp [hexAWOriginCoord] at hwhite
  · rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp r (by
      simpa only [hlhd_intervalCore_length] using hr)]
    apply hlhd_normalized_depth_pos ts hleg p
      (hlhd_intervalUp_bridge ts hleg hhalf p hp)
    · omega
    · rw [hlhd_intervalCore_length, hraw] at hr
      omega

theorem hlhd_white_depth_mem_horizontal (T : ℕ) (c : HexAWCoord)
    (hwhite : c.color = .white) (hpos : 0 < hexAWDepth c)
    (hupper : hexAWDepth c ≤ T) :
    0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * T := by
  simp only [hexAWBookRe2, hwhite]
  constructor <;> omega

theorem hlhd_span_eq_width (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) :
    hlhr_intervalSpan (hlhd_height ts hleg) p = hlhd_width ts hleg p := by
  simp only [hlhr_intervalSpan, hlhd_height, hlhd_width, hlhd_delta]
  rw [← Int.cast_sub]
  rw [← hlhr_natAbs_cast]

theorem hlhd_width_pos_of_span_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ)
    (hp : 0 < hlhr_intervalSpan (hlhd_height ts hleg) p) :
    0 < hlhd_width ts hleg p := by
  rw [hlhd_span_eq_width] at hp
  exact_mod_cast hp

theorem hlhd_width_gt_of_span_gt (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p q : ℕ × ℕ)
    (hpq : hlhr_intervalSpan (hlhd_height ts hleg) p >
      hlhr_intervalSpan (hlhd_height ts hleg) q) :
    hlhd_width ts hleg p > hlhd_width ts hleg q := by
  rw [hlhd_span_eq_width, hlhd_span_eq_width] at hpq
  exact_mod_cast hpq

theorem hlhd_interval_bounds (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    ∀ p ∈ hlhd_intervals ts hleg, p.1 < p.2 ∧ p.2 ≤ ts.length := by
  intro p hp
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhd_intervals, hempty, hlhr_intervalsAux] at hp
  exact hlhr_intervalsAux_bounds (hlhd_height ts hleg) ts.length
    ts.length 0 true (List.length_pos_iff.mpr hne)
      (hlhd_halfSpace_ahead ts hleg hhalf) p hp |>.2


end
end StatMech.Universality
