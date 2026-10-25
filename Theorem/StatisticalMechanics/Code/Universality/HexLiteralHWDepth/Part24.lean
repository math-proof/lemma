/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part22


namespace StatMech.Universality

open HexWalk

noncomputable section

@[simp] theorem hlhd_contentHalf_turns (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    hhc_halfTurns (hlhd_contentHalf ts hleg hhalf) = ts :=
  hlhd_bridgeList_contents ts hleg hhalf

theorem hlhd_interval_width_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    0 < hlhd_width ts hleg p := by
  simpa [hlhd_bridge] using
    (hlhd_bridge ts hleg hhalf ⟨p, hp⟩).width_pos

theorem hlhd_neighbor_white_of_black {c d : HexAWCoord} {e : Fin 3}
    (hc : c.color = .black) (he : hexAWNeighbor c e = d) :
    d.color = .white := by
  subst d
  rcases c with ⟨i, j, color⟩
  cases color <;> simp_all
  fin_cases e <;> rfl


theorem hlhd_intervalEndpoint_mid_incident_horizontal (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (k : ℕ)
    (hk : k < (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
    ∃ c : HexAWCoord, ∃ e : Fin 3,
      hexInfra_midAccum hexAWStart 1
          ((hlhd_intervalEndpoint ts hleg hhalf p hp).take k) =
        hexAWMid c e ∧
      0 ≤ hexAWBookRe2 c ∧
        hexAWBookRe2 c ≤ 3 * hlhd_width ts hleg p := by
  have hwidth := hlhd_interval_width_pos ts hleg hhalf p hp
  by_cases hk0 : k = 0
  · subst k
    refine ⟨hexAWOriginCoord, 0, ?_, ?_⟩
    · simp
    · simp [hexAWBookRe2, hexAWOriginCoord, hexAWDepth, hexAWLong]
      omega
  · let out := hlhd_intervalEndpoint ts hleg hhalf p hp
    let hout := hlhd_intervalEndpoint_endpointIsLegalSAW ts hleg hhalf p hp
    let core := hlhd_intervalCore ts hleg hhalf p hp
    let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkcore : k ≤ core.length := by
      exact hlhd_intervalEndpoint_index_le_core ts hleg hhalf p hp hk
    have hkprevcore : k - 1 ≤ core.length := by omega
    have hkprevout : k - 1 < out.length := by
      change k - 1 <
        (hlhd_intervalEndpoint ts hleg hhalf p hp).length
      omega
    obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent_legal
      out hout.1 (k - 1) hkprevout
    have hsucc : k - 1 + 1 = k := by omega
    rw [hsucc] at he
    have hmid := hlhd_midAccum_prefixEdge out hout.1 k hkpos
      (Nat.le_of_lt (show k < out.length by exact hk)) e he
    let a := hlhc_prefixCoord out hout.1 (k - 1)
    let b := hlhc_prefixCoord out hout.1 k
    change hexAWNeighbor a e = b at he
    change hexInfra_midAccum hexAWStart 1 (out.take k) =
      hexAWMid a e at hmid
    have ha : a = hlhc_prefixCoord core hcore.1 (k - 1) := by
      exact hlhd_intervalEndpoint_prefixCoord_eq_core
        ts hleg hhalf p hp (k - 1) hkprevcore
    have hb : b = hlhc_prefixCoord core hcore.1 k := by
      exact hlhd_intervalEndpoint_prefixCoord_eq_core
        ts hleg hhalf p hp k hkcore
    by_cases haw : a.color = .white
    · have hawCore :
          (hlhc_prefixCoord core hcore.1 (k - 1)).color = .white := by
        simpa only [ha] using haw
      have hpos := hlhd_intervalCore_white_depth_pos
        ts hleg hhalf p hp (k - 1) hkprevcore hawCore
      have hupper :=
        (hlhd_intervalCore_depth_bounds
          ts hleg hhalf p hp (k - 1) hkprevcore).2
      refine ⟨a, e, hmid, ?_⟩
      simpa only [ha] using hlhd_white_depth_mem_horizontal
        (hlhd_width ts hleg p) _ hawCore hpos hupper
    · have hablack : a.color = .black := by
        cases hc : a.color <;> simp_all
      have hbwhite : b.color = .white :=
        hlhd_neighbor_white_of_black hablack he
      have hbwhiteCore :
          (hlhc_prefixCoord core hcore.1 k).color = .white := by
        simpa only [hb] using hbwhite
      have hpos := hlhd_intervalCore_white_depth_pos
        ts hleg hhalf p hp k hkcore hbwhiteCore
      have hupper :=
        (hlhd_intervalCore_depth_bounds
          ts hleg hhalf p hp k hkcore).2
      have hswap : hexAWMid a e = hexAWMid b e := by
        rw [← he]
        exact (hexAWMid_neighbor a e).symm
      refine ⟨b, e, hmid.trans hswap, ?_⟩
      simpa only [hb] using hlhd_white_depth_mem_horizontal
        (hlhd_width ts hleg p) _ hbwhiteCore hpos hupper

end
end StatMech.Universality
