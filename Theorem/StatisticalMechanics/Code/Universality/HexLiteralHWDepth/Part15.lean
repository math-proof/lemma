/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part13


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_endpointTurns_length (exits : Bool) (exitTurn : ℤ)
    (core : List ℤ) :
    (hlhd_endpointTurns exits exitTurn core).length = core.length ∨
      (hlhd_endpointTurns exits exitTurn core).length = core.length + 1 := by
  cases exits <;> simp [hlhd_endpointTurns]

theorem hlhd_coreTurns_length {raw : List ℤ} (hraw : raw ≠ [])
    (entry : ℤ) :
    (hlhd_coreTurns entry raw).length = raw.length := by
  cases raw with
  | nil => exact (hraw rfl).elim
  | cons t tail => simp [hlhd_coreTurns]

theorem hlhd_decodeColumn_encode {raw : List ℤ} (hraw : raw ≠ [])
    (hlegal : ∀ t ∈ raw, t = 1 ∨ t = -1)
    (up exits : Bool) (entry exitTurn : ℤ) :
    hlhd_decodeColumn
        ⟨up, hlhd_turnBit raw.head!, exits⟩
        (hlhd_endpointTurns exits exitTurn (hlhd_coreTurns entry raw)) = raw := by
  cases raw with
  | nil => exact (hraw rfl).elim
  | cons t tail =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      cases exits with
      | false =>
          simp [hlhd_decodeColumn, hlhd_endpointTurns, hlhd_coreTurns,
            hlhd_bitTurn_turnBit ht]
      | true =>
          simp only [hlhd_decodeColumn, hlhd_endpointTurns, ↓reduceIte,
            hlhd_coreTurns, List.tail_cons]
          rw [List.dropLast_append_of_ne_nil
            (by simp : [exitTurn] ≠ []), List.dropLast_singleton,
            List.append_nil, List.tail_cons]
          change hlhd_bitTurn (hlhd_turnBit t) :: tail = t :: tail
          rw [hlhd_bitTurn_turnBit ht]


theorem hlhd_raw_eq_of_tagged_eq
    {raw raw' : List ℤ} (hraw : raw ≠ []) (hraw' : raw' ≠ [])
    (hlegal : ∀ t ∈ raw, t = 1 ∨ t = -1)
    (hlegal' : ∀ t ∈ raw', t = 1 ∨ t = -1)
    {up up' exits exits' : Bool} {entry entry' exitTurn exitTurn' : ℤ}
    (htag : (HLHDColumnTag.mk up (hlhd_turnBit raw.head!) exits) =
      HLHDColumnTag.mk up' (hlhd_turnBit raw'.head!) exits')
    (hout : hlhd_endpointTurns exits exitTurn (hlhd_coreTurns entry raw) =
      hlhd_endpointTurns exits' exitTurn' (hlhd_coreTurns entry' raw')) :
    raw = raw' := by
  have hdecode :
      hlhd_decodeColumn
          ⟨up, hlhd_turnBit raw.head!, exits⟩
          (hlhd_endpointTurns exits exitTurn (hlhd_coreTurns entry raw)) =
        hlhd_decodeColumn
          ⟨up', hlhd_turnBit raw'.head!, exits'⟩
          (hlhd_endpointTurns exits' exitTurn'
            (hlhd_coreTurns entry' raw')) := by
    rw [htag, hout]
  rw [hlhd_decodeColumn_encode hraw hlegal up exits entry exitTurn,
    hlhd_decodeColumn_encode hraw' hlegal' up' exits' entry' exitTurn'] at hdecode
  exact hdecode


theorem hlhd_interval_legal (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    {p : ℕ × ℕ} (hp : p ∈ hlhd_intervals ts hleg) :
    (ofTurns (hlhr_pieceMid hexAWStart 1 ts p.1)
      (hlhr_pieceHead 1 ts p.1) (hlhr_intervalContent ts p)).IsLegalSAW := by
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhd_intervals, hempty, hlhr_intervalsAux] at hp
  have hb := hlhr_intervalsAux_bounds (hlhd_height ts hleg) ts.length
    ts.length 0 true (List.length_pos_iff.mpr hne)
      (hlhd_halfSpace_ahead ts hleg hhalf) p hp
  obtain ⟨hp12, hp2len⟩ := hb.2
  unfold hlhr_intervalContent
  apply hlhr_slice_legal hexAWStart 1 ts hleg
  omega

theorem hlhd_intervalContent_ne (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    {p : ℕ × ℕ} (hp : p ∈ hlhd_intervals ts hleg) :
    hlhr_intervalContent ts p ≠ [] := by
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhd_intervals, hempty, hlhr_intervalsAux] at hp
  have hb := hlhr_intervalsAux_bounds (hlhd_height ts hleg) ts.length
    ts.length 0 true (List.length_pos_iff.mpr hne)
      (hlhd_halfSpace_ahead ts hleg hhalf) p hp
  obtain ⟨hp12, hp2len⟩ := hb.2
  unfold hlhr_intervalContent
  have htake : p.2 - p.1 ≤ (ts.drop p.1).length := by
    simp only [List.length_drop]
    omega
  intro hnil
  have hlen := congrArg List.length hnil
  rw [List.length_take_of_le htake] at hlen
  simp only [List.length_nil] at hlen
  omega


theorem hlhd_coreTurns_isLegalSAW
    {m : ℂ} {h : ℤ} {raw : List ℤ}
    (hraw : (ofTurns m h raw).IsLegalSAW) (hrawne : raw ≠ [])
    {entry : ℤ} (hentry : entry = 1 ∨ entry = -1) :
    (ofTurns hexAWStart 1 (hlhd_coreTurns entry raw)).IsLegalSAW := by
  cases raw with
  | nil => exact (hrawne rfl).elim
  | cons t tail =>
      have ht : t = 1 ∨ t = -1 := hraw.1 t (by simp)
      let h' : ℤ := 1 + entry - t
      let m' : ℂ := -halfStep h'
      have hrebase : (ofTurns m' h' (t :: tail)).IsLegalSAW :=
        (hhe_isLegalSAW_rebase m m' h h' (t :: tail)).mpr hraw
      constructor
      · intro u hu
        change u ∈ entry :: tail at hu
        simp only [List.mem_cons] at hu
        rcases hu with hueq | hu
        · rw [hueq]
          exact hentry
        · exact hraw.1 u (List.mem_cons_of_mem t hu)
      · change (verticesAux hexAWStart 1 (entry :: tail)).Nodup
        have hzero : hexAWStart + halfStep 1 = 0 := by
          unfold hexAWStart halfStep
          rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
          ring
        have hverts :
            verticesAux hexAWStart 1 (entry :: tail) =
              verticesAux m' h' (t :: tail) := by
          simp only [verticesAux_cons]
          congr 1
          · dsimp [m']
            rw [hzero]
            ring
          · have hh : h' + t = 1 + entry := by
              dsimp [h']
              ring
            rw [hh]
            dsimp [m']
            rw [hzero]
            ring_nf
        rw [hverts]
        exact hrebase.2

theorem hlhd_coreTurns_vertices {raw : List ℤ} (hrawne : raw ≠ [])
    (entry : ℤ) :
    verticesAux hexAWStart 1 (hlhd_coreTurns entry raw) =
      verticesAux (-halfStep (1 + entry - raw.head!))
        (1 + entry - raw.head!) raw := by
  cases raw with
  | nil => exact (hrawne rfl).elim
  | cons t tail =>
      have hzero : hexAWStart + halfStep 1 = 0 := by
        unfold hexAWStart halfStep
        rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
        ring
      simp only [hlhd_coreTurns, List.tail_cons, verticesAux_cons,
        List.head!_cons]
      congr 1
      · rw [hzero]
        ring
      · have hh : 1 + entry - t + t = 1 + entry := by ring
        rw [hh, hzero]
        ring_nf

theorem hlhd_endpointTurns_endpointIsLegalSAW
    {core : List ℤ} (hcore : (ofTurns hexAWStart 1 core).IsLegalSAW)
    (exits : Bool) {exitTurn : ℤ}
    (hexit : exitTurn = 1 ∨ exitTurn = -1) :
    (ofTurns hexAWStart 1
      (hlhd_endpointTurns exits exitTurn core)).EndpointIsLegalSAW := by
  cases exits with
  | false =>
      exact hcore.endpointIsLegalSAW
  | true =>
      exact (endpointIsLegalSAW_append_one_iff
        hexAWStart 1 core exitTurn).2 ⟨hcore, hexit⟩


end
end StatMech.Universality
