/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part16


namespace StatMech.Universality

open HexWalk

noncomputable section

@[simp] theorem hlhd_intervalNormalizedCoords_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (hlhd_intervalNormalizedCoords ts hleg hhalf p hp).length =
      (hlhd_intervalRaw ts p).length + 1 := by
  simp [hlhd_intervalNormalizedCoords, hlhd_intervalCoords]

theorem hlhd_intervalNormalizedCoords_getElem (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (r : ℕ) (hr : r < (hlhd_intervalNormalizedCoords ts hleg hhalf p hp).length) :
    (hlhd_intervalNormalizedCoords ts hleg hhalf p hp)[r] =
      hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 (p.1 + r)) := by
  unfold hlhd_intervalNormalizedCoords hlhd_intervalCoords
  rw [List.getElem_map, List.getElem_ofFn]

theorem hlhd_intervalCore_vertices_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    verticesAux hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp) =
      (hlhd_intervalNormalizedCoords ts hleg hhalf p hp).map hexAWPos := by
  let up := hlhd_intervalUp ts hleg hhalf p hp
  let source := hlhc_prefixCoord ts hleg.1 p.1
  have hcdir := hlhd_bridge_source_color ts hleg p
    (hlhd_interval_index_bounds ts hleg hhalf p hp).2
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
  have hsource : if up then source.color = .black else source.color = .white := by
    cases hup : up <;> simpa [up, hup, source] using hcdir
  rw [hlhd_intervalCore_vertices_affine ts hleg hhalf p hp,
    hlhd_intervalRaw_vertices_pos ts hleg hhalf p hp]
  unfold hlhd_intervalNormalizedCoords
  simp only [List.map_map, Function.comp_apply]
  apply List.map_congr_left
  intro c hc
  change (if up then hexAWPos c - hexAWPos source else hexAWPos source - hexAWPos c) =
    hexAWPos (hlhd_normalizeCoord up source c)
  exact (hlhd_normalizeCoord_pos up source c hsource).symm

theorem hlhd_intervalRaw_legal (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    ∀ t ∈ hlhd_intervalRaw ts p, t = 1 ∨ t = -1 := by
  exact (hlhd_interval_legal ts hleg hhalf hp).1

theorem hlhd_intervalCore_isLegalSAW (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (ofTurns hexAWStart 1
      (hlhd_intervalCore ts hleg hhalf p hp)).IsLegalSAW := by
  exact hlhd_coreTurns_isLegalSAW
    (hlhd_interval_legal ts hleg hhalf hp)
    (hlhd_intervalRaw_ne ts hleg hhalf p hp)
    (hlhd_entryTurn_legal _)

theorem hlhd_intervalCore_prefixCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (r : ℕ) (hr : r ≤ (hlhd_intervalRaw ts p).length) :
    hlhc_prefixCoord (hlhd_intervalCore ts hleg hhalf p hp)
        (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r =
      hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 (p.1 + r)) := by
  let core := hlhd_intervalCore ts hleg hhalf p hp
  let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
  let cs := hlhd_intervalNormalizedCoords ts hleg hhalf p hp
  have hcorelen : core.length = (hlhd_intervalRaw ts p).length := by
    exact hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
      (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hrCore : r ≤ core.length := by rw [hcorelen]; exact hr
  have hrmap : r < (cs.map hexAWPos).length := by
    simp only [List.length_map]
    change r < cs.length
    dsimp [cs]
    rw [hlhd_intervalNormalizedCoords_length]
    omega
  have hget := hexJordan_verticesAux_getElem?_eq
    hexAWStart 1 core r hrCore
  rw [hlhd_intervalCore_vertices_pos ts hleg hhalf p hp,
    List.getElem?_eq_getElem hrmap, Option.some.injEq] at hget
  rw [List.getElem_map] at hget
  have hcget := hlhd_intervalNormalizedCoords_getElem
    ts hleg hhalf p hp r (by
      rw [hlhd_intervalNormalizedCoords_length]
      omega)
  rw [hcget] at hget
  apply hexAWPos_injective
  exact (hlhc_prefixCoord_vertex core hcore.1 r).symm.trans hget.symm


theorem hlhd_endsAt_lastPrefixEdge (ws : List ℤ)
    (hws : (ofTurns hexAWStart 1 ws).IsLegalSAW) (hne : ws ≠ [])
    (e : Fin 3)
    (he : hexAWNeighbor
      (hlhc_prefixCoord ws hws.1 (ws.length - 1)) e =
        hlhc_prefixCoord ws hws.1 ws.length) :
    (ofTurns hexAWStart 1 ws).EndsAt
      (hexAWMid (hlhc_prefixCoord ws hws.1 (ws.length - 1)) e) := by
  have hnpos : 0 < ws.length := List.length_pos_iff.mpr hne
  have hk : ws.length - 1 < ws.length := by omega
  have hprev := hexEndpoint_vertexPos_eq_nextMid_sub ws (ws.length - 1) hk
  have hprevPos := hlhc_prefixCoord_vertex ws hws.1 (ws.length - 1)
  have hfinalPos := hlhc_prefixCoord_vertex ws hws.1 ws.length
  have hsubadd : ws.length - 1 + 1 = ws.length := by omega
  rw [hsubadd, List.take_length] at hprev
  unfold hexJordan_vertexPos at hprev
  rw [List.take_length] at hfinalPos
  unfold HexWalk.EndsAt
  rw [hexInfra_endMid_eq_midAccum]
  unfold hexAWMid
  rw [he]
  rw [← hprevPos, ← hfinalPos]
  rw [hprev]
  ring

theorem hlhd_neighbor_black_max_edge_zero (c d : HexAWCoord) (e : Fin 3)
    (he : hexAWNeighbor c e = d) (hd : d.color = .black)
    (hdepth : hexAWDepth c ≤ hexAWDepth d) : e = 0 := by
  rcases hlhd_neighbor_depth_cases c e with hinc | hdec | hflat
  · exfalso
    apply hexAWNeighbor_color_ne c e
    rw [he, hd, hinc.2.1]
  · have hdeq := congrArg hexAWDepth he
    rw [hdec.1] at hdeq
    omega
  · exact hflat.2

end
end StatMech.Universality
