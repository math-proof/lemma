/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhc_prefixCoord_eq_endpointPrefixCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (k : ℕ) :
    hlhc_prefixCoord ts hleg.1 k =
      hexEndpointPrefixCoord ts hleg.1 k := by
  unfold hlhc_prefixCoord hexEndpointPrefixCoord
  congr

theorem hlhc_prefixCoord_adjacent (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (k : ℕ) (hk : k < ts.length) :
    ∃ e : Fin 3,
      hexAWNeighbor (hlhc_prefixCoord ts hleg.1 k) e =
        hlhc_prefixCoord ts hleg.1 (k + 1) := by
  simpa only [hlhc_prefixCoord_eq_endpointPrefixCoord] using
    hexEndpointPrefixCoord_adjacent ts hleg.1 k hk

theorem hlhc_prefixCoord_adjacent_legal (ts : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns)
    (k : ℕ) (hk : k < ts.length) :
    ∃ e : Fin 3,
      hexAWNeighbor (hlhc_prefixCoord ts hlegal k) e =
        hlhc_prefixCoord ts hlegal (k + 1) := by
  have hcoord (r : ℕ) :
      hlhc_prefixCoord ts hlegal r =
        hexEndpointPrefixCoord ts hlegal r := by
    unfold hlhc_prefixCoord hexEndpointPrefixCoord
    congr
  simpa only [hcoord] using
    hexEndpointPrefixCoord_adjacent ts hlegal k hk


theorem hlhd_prefix_edge_unit (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (k : ℕ) (hk : k < ts.length) (e : Fin 3)
    (he : hexAWNeighbor (hlhc_prefixCoord ts hleg.1 k) e =
      hlhc_prefixCoord ts hleg.1 (k + 1)) :
    hexUnit (hexInfra_headAccum 1 (ts.take (k + 1))) =
      hexUnit (hexAWHeading (hlhc_prefixCoord ts hleg.1 k) e) := by
  have hstep :
      hexJordan_vertexPos hexAWStart 1 ts (k + 1) -
          hexJordan_vertexPos hexAWStart 1 ts k =
        hexUnit (hexInfra_headAccum 1 (ts.take (k + 1))) := by
    rw [hexEndpoint_vertexPos_eq_nextMid_sub ts k hk]
    unfold hexJordan_vertexPos
    unfold halfStep
    ring
  have hkpos : hexJordan_vertexPos hexAWStart 1 ts k =
      hexAWPos (hlhc_prefixCoord ts hleg.1 k) := by
    simpa only [hexJordan_vertexPos] using
      hlhc_prefixCoord_vertex ts hleg.1 k
  have hsuccpos : hexJordan_vertexPos hexAWStart 1 ts (k + 1) =
      hexAWPos (hlhc_prefixCoord ts hleg.1 (k + 1)) := by
    simpa only [hexJordan_vertexPos] using
      hlhc_prefixCoord_vertex ts hleg.1 (k + 1)
  rw [hkpos, hsuccpos] at hstep
  have hcoord :
      hexAWPos (hlhc_prefixCoord ts hleg.1 (k + 1)) -
          hexAWPos (hlhc_prefixCoord ts hleg.1 k) =
        hexUnit (hexAWHeading (hlhc_prefixCoord ts hleg.1 k) e) := by
    rw [← he]
    exact hexAWPos_neighbor _ _
  exact hstep.symm.trans hcoord


theorem hlhd_midAccum_prefixEdge (ts : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns)
    (k : ℕ) (hkpos : 0 < k) (hkle : k ≤ ts.length)
    (e : Fin 3)
    (he : hexAWNeighbor (hlhc_prefixCoord ts hlegal (k - 1)) e =
      hlhc_prefixCoord ts hlegal k) :
    hexInfra_midAccum hexAWStart 1 (ts.take k) =
      hexAWMid (hlhc_prefixCoord ts hlegal (k - 1)) e := by
  have hk : k - 1 < ts.length := by omega
  have hprev := hexEndpoint_vertexPos_eq_nextMid_sub ts (k - 1) hk
  have hprevPos := hlhc_prefixCoord_vertex ts hlegal (k - 1)
  have hfinalPos := hlhc_prefixCoord_vertex ts hlegal k
  have hsubadd : k - 1 + 1 = k := by omega
  rw [hsubadd] at hprev
  unfold hexJordan_vertexPos at hprev
  unfold hexAWMid
  rw [he]
  rw [← hprevPos, ← hfinalPos]
  rw [hprev]
  ring


theorem hlhc_prefixCoord_append_single (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (t : ℤ)
    (hleg' : (ofTurns hexAWStart 1 (ts ++ [t])).IsLegalSAW)
    (k : ℕ) (hk : k ≤ ts.length) :
    hlhc_prefixCoord (ts ++ [t]) hleg'.1 k =
      hlhc_prefixCoord ts hleg.1 k := by
  apply hexAWPos_injective
  rw [← hlhc_prefixCoord_vertex (ts ++ [t]) hleg'.1 k,
    ← hlhc_prefixCoord_vertex ts hleg.1 k,
    List.take_append_of_le_length hk]

theorem hlhd_neighbor_depth_cases (c : HexAWCoord) (e : Fin 3) :
    (hexAWDepth (hexAWNeighbor c e) = hexAWDepth c + 1 ∧
        c.color = .black ∧ (e = 1 ∨ e = 2)) ∨
      (hexAWDepth (hexAWNeighbor c e) = hexAWDepth c - 1 ∧
        c.color = .white ∧ (e = 1 ∨ e = 2)) ∨
      (hexAWDepth (hexAWNeighbor c e) = hexAWDepth c ∧ e = 0) := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;>
    simp [hexAWNeighbor, hexAWDepth, hexAWLong] <;> omega


end
end StatMech.Universality
