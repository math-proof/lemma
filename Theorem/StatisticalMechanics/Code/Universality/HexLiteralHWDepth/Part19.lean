/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part17


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_intervalLastEdge_normalized (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWNeighbor (hlhd_intervalPrevCoord ts hleg hhalf p hp)
        (hlhd_intervalLastEdge ts hleg hhalf p hp) =
      hlhd_intervalFarCoord ts hleg hhalf p hp := by
  unfold hlhd_intervalPrevCoord hlhd_intervalFarCoord
  rw [← hlhd_normalizeCoord_neighbor]
  exact congrArg
    (hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
      (hlhc_prefixCoord ts hleg.1 p.1))
    (hlhd_intervalLastEdge_spec ts hleg hhalf p hp)

theorem hlhd_intervalCore_lastEdge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    let core := hlhd_intervalCore ts hleg hhalf p hp
    let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
    hexAWNeighbor (hlhc_prefixCoord core hcore.1 (core.length - 1))
        (hlhd_intervalLastEdge ts hleg hhalf p hp) =
      hlhc_prefixCoord core hcore.1 core.length := by
  dsimp only
  let core := hlhd_intervalCore ts hleg hhalf p hp
  let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
  let n := (hlhd_intervalRaw ts p).length
  have hn : 0 < n := List.length_pos_iff.mpr
    (hlhd_intervalRaw_ne ts hleg hhalf p hp)
  have hcorelen : core.length = n := by
    exact hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
      (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hnval : n = p.2 - p.1 :=
    hlhd_intervalRaw_length ts hleg hhalf p hp
  have hprevIndex : p.1 + (n - 1) = p.2 - 1 := by omega
  have hfarIndex : p.1 + n = p.2 := by
    have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
    omega
  rw [hcorelen]
  rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp (n - 1) (by omega),
    hlhd_intervalCore_prefixCoord ts hleg hhalf p hp n le_rfl,
    hprevIndex, hfarIndex]
  exact hlhd_intervalLastEdge_normalized ts hleg hhalf p hp

theorem hlhd_intervalCore_endsAt (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (ofTurns hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp)).EndsAt
      (hexAWMid (hlhd_intervalPrevCoord ts hleg hhalf p hp)
        (hlhd_intervalLastEdge ts hleg hhalf p hp)) := by
  let core := hlhd_intervalCore ts hleg hhalf p hp
  let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
  have hne : core ≠ [] := by
    dsimp [core, hlhd_intervalCore, hlhd_coreTurns]
    simp
  have hend := hlhd_endsAt_lastPrefixEdge core hcore hne
    (hlhd_intervalLastEdge ts hleg hhalf p hp)
    (hlhd_intervalCore_lastEdge ts hleg hhalf p hp)
  have hcorelen : core.length = (hlhd_intervalRaw ts p).length :=
    hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
      (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hnval := hlhd_intervalRaw_length ts hleg hhalf p hp
  have hidx : p.1 + (core.length - 1) = p.2 - 1 := by
    have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
    omega
  rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp
    (core.length - 1) (by rw [hcorelen]; omega), hidx] at hend
  exact hend

theorem hlhd_intervalEndpoint_endpointIsLegalSAW (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (ofTurns hexAWStart 1
      (hlhd_intervalEndpoint ts hleg hhalf p hp)).EndpointIsLegalSAW := by
  exact hlhd_endpointTurns_endpointIsLegalSAW
    (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp)
    (hlhd_intervalExits ts hleg hhalf p hp)
    (hlhd_exitTurn_legal _)

theorem hlhd_interval_decode (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hlhd_decodeColumn (hlhd_intervalTag ts hleg hhalf p hp)
        (hlhd_intervalEndpoint ts hleg hhalf p hp) =
      hlhd_intervalRaw ts p := by
  exact hlhd_decodeColumn_encode
    (hlhd_intervalRaw_ne ts hleg hhalf p hp)
    (hlhd_intervalRaw_legal ts hleg hhalf p hp)
    (hlhd_intervalUp ts hleg hhalf p hp)
    (hlhd_intervalExits ts hleg hhalf p hp)
    (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
    (hlhd_exitTurn (hlhd_intervalLastEdge ts hleg hhalf p hp))

theorem hlhd_intervalEndpoint_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (hlhd_intervalEndpoint ts hleg hhalf p hp).length =
        (hlhd_intervalRaw ts p).length ∨
      (hlhd_intervalEndpoint ts hleg hhalf p hp).length =
        (hlhd_intervalRaw ts p).length + 1 := by
  have hcore := hlhd_coreTurns_length
    (hlhd_intervalRaw_ne ts hleg hhalf p hp)
    (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hout := hlhd_endpointTurns_length
    (hlhd_intervalExits ts hleg hhalf p hp)
    (hlhd_exitTurn (hlhd_intervalLastEdge ts hleg hhalf p hp))
    (hlhd_intervalCore ts hleg hhalf p hp)
  simpa [hlhd_intervalEndpoint, hlhd_intervalCore, hcore] using hout

@[simp] theorem hlhd_intervalCore_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (hlhd_intervalCore ts hleg hhalf p hp).length =
      (hlhd_intervalRaw ts p).length :=
  hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
    (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))

theorem hlhd_intervalEndpoint_index_le_core (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    {k : ℕ}
    (hk : k < (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
    k ≤ (hlhd_intervalCore ts hleg hhalf p hp).length := by
  rw [hlhd_intervalCore_length]
  cases hexits : hlhd_intervalExits ts hleg hhalf p hp <;>
    simp [hlhd_intervalEndpoint, hlhd_endpointTurns, hexits] at hk <;>
    omega

theorem hlhd_intervalEndpoint_prefixCoord_eq_core (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (k : ℕ)
    (hk : k ≤ (hlhd_intervalCore ts hleg hhalf p hp).length) :
    hlhc_prefixCoord (hlhd_intervalEndpoint ts hleg hhalf p hp)
        (hlhd_intervalEndpoint_endpointIsLegalSAW
          ts hleg hhalf p hp).1 k =
      hlhc_prefixCoord (hlhd_intervalCore ts hleg hhalf p hp)
        (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 k := by
  apply hexAWPos_injective
  rw [← hlhc_prefixCoord_vertex
      (hlhd_intervalEndpoint ts hleg hhalf p hp)
      (hlhd_intervalEndpoint_endpointIsLegalSAW ts hleg hhalf p hp).1 k,
    ← hlhc_prefixCoord_vertex
      (hlhd_intervalCore ts hleg hhalf p hp)
      (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 k]
  have htake :
      (hlhd_intervalEndpoint ts hleg hhalf p hp).take k =
        (hlhd_intervalCore ts hleg hhalf p hp).take k := by
    cases hexits : hlhd_intervalExits ts hleg hhalf p hp
    · simp [hlhd_intervalEndpoint, hlhd_endpointTurns, hexits]
    · simp only [hlhd_intervalEndpoint, hlhd_endpointTurns, hexits,
        ↓reduceIte]
      exact List.take_append_of_le_length hk
  rw [htake]


end
end StatMech.Universality
