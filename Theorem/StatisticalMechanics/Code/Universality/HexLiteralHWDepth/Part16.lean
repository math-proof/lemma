/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part14


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_intervalRaw_ne (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hlhd_intervalRaw ts p ≠ [] :=
  hlhd_intervalContent_ne ts hleg hhalf hp

theorem hlhd_intervalRaw_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (hlhd_intervalRaw ts p).length = p.2 - p.1 := by
  unfold hlhd_intervalRaw hlhr_intervalContent
  rw [List.length_take_of_le]
  simp only [List.length_drop]
  exact Nat.sub_le_sub_right
    (hlhd_interval_index_bounds ts hleg hhalf p hp).2 p.1

theorem hlhd_intervalRaw_head_step (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexInfra_headAccum 1 (ts.take (p.1 + 1)) =
      hexInfra_headAccum 1 (ts.take p.1) +
        (hlhd_intervalRaw ts p).head! := by
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  have hk : p.1 < ts.length := lt_of_lt_of_le hb.1 hb.2
  have hhead : (hlhd_intervalRaw ts p).head! = ts[p.1] := by
    have hdrop : ts.drop p.1 = ts[p.1] :: ts.drop (p.1 + 1) :=
      List.drop_eq_getElem_cons hk
    unfold hlhd_intervalRaw hlhr_intervalContent
    change ((ts.drop p.1).take (p.2 - p.1)).head! = ts[p.1]
    have hdiff : 0 < p.2 - p.1 := Nat.sub_pos_of_lt hb.1
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdiff)
    rw [hn, hdrop]
    rfl
  have htake : ts.take (p.1 + 1) = ts.take p.1 ++ [ts[p.1]] :=
    List.take_succ_eq_append_getElem hk
  simp only [hexInfra_headAccum_eq_add_sum]
  change 1 + (ts.take (p.1 + 1)).sum =
    1 + (ts.take p.1).sum + (hlhd_intervalRaw ts p).head!
  rw [htake]
  rw [hhead]
  simp only [List.sum_append, List.sum_singleton]
  ring

theorem hlhd_interval_entry_unit (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexUnit (1 + hlhd_entryTurn
        (hlhd_intervalFirstEdge ts hleg hhalf p hp)) =
      if hlhd_intervalUp ts hleg hhalf p hp then
        hexUnit (hexInfra_headAccum 1 (ts.take (p.1 + 1)))
      else -hexUnit (hexInfra_headAccum 1 (ts.take (p.1 + 1))) := by
  let up := hlhd_intervalUp ts hleg hhalf p hp
  let e := hlhd_intervalFirstEdge ts hleg hhalf p hp
  let c := hlhc_prefixCoord ts hleg.1 p.1
  have hunit :
      hexUnit (hexInfra_headAccum 1 (ts.take (p.1 + 1))) =
        hexUnit (hexAWHeading c e) :=
    hlhd_prefix_edge_unit ts hleg p.1
      (lt_of_lt_of_le
        (hlhd_interval_index_bounds ts hleg hhalf p hp).1
        (hlhd_interval_index_bounds ts hleg hhalf p hp).2)
      e (hlhd_intervalFirstEdge_spec ts hleg hhalf p hp)
  have hin : e = 1 ∨ e = 2 :=
    hlhd_intervalFirstEdge_inward ts hleg hhalf p hp
  have hcdir := hlhd_bridge_source_color ts hleg p
    (hlhd_interval_index_bounds ts hleg hhalf p hp).2
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
  cases hup : up with
  | false =>
      have hc : c.color = .white := by
        simpa [up, hup, c] using hcdir
      simp only [up, hup, Bool.false_eq_true, ↓reduceIte]
      change hexUnit (1 + hlhd_entryTurn e) = -hexUnit _
      rcases hin with he | he
      · rw [he] at hunit ⊢
        rw [hunit]
        have h3 := hexUnit_add_three 0
        simp [c, hc, hlhd_entryTurn, hexAWHeading] at h3 ⊢
        rw [h3]
        ring
      · rw [he] at hunit ⊢
        rw [hunit]
        have h5 := hexUnit_add_three 2
        simp [c, hc, hlhd_entryTurn, hexAWHeading] at h5 ⊢
        rw [h5]
        ring
  | true =>
      have hc : c.color = .black := by
        simpa [up, hup, c] using hcdir
      simp only [up, hup, ↓reduceIte]
      change hexUnit (1 + hlhd_entryTurn e) = hexUnit _
      rcases hin with he | he <;>
        rw [he] at hunit ⊢ <;>
        simpa [c, hc, hlhd_entryTurn, hexAWHeading] using hunit.symm

theorem hlhd_interval_rho (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    let raw := hlhd_intervalRaw ts p
    let entry := hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp)
    let h0 := hexInfra_headAccum 1 (ts.take p.1)
    let h' := 1 + entry - raw.head!
    hhe_rho h0 h' =
      if hlhd_intervalUp ts hleg hhalf p hp then 1 else -1 := by
  dsimp only
  let raw := hlhd_intervalRaw ts p
  let entry := hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp)
  let h0 := hexInfra_headAccum 1 (ts.take p.1)
  let hout := hexInfra_headAccum 1 (ts.take (p.1 + 1))
  let h' := 1 + entry - raw.head!
  let v := halfStep hout
  have hhout : h0 + raw.head! = hout := by
    exact (hlhd_intervalRaw_head_step ts hleg hhalf p hp).symm
  have hhentry : h' + raw.head! = 1 + entry := by
    dsimp [h']
    ring
  have hunit := hlhd_interval_entry_unit ts hleg hhalf p hp
  change hexUnit (1 + entry) =
    if hlhd_intervalUp ts hleg hhalf p hp then hexUnit hout else -hexUnit hout at hunit
  have hentryHalf : halfStep (1 + entry) =
      if hlhd_intervalUp ts hleg hhalf p hp then v else -v := by
    change halfStep (1 + entry) =
      if hlhd_intervalUp ts hleg hhalf p hp then halfStep hout else -halfStep hout
    unfold halfStep
    rw [hunit]
    split <;> ring
  have hshift := hhe_halfStep_shift h0 h' raw.head!
  rw [hhentry, hhout, hentryHalf] at hshift
  have hv : v ≠ 0 := by
    dsimp [v]
    exact hexConcrete_halfStep_ne _
  cases hup : hlhd_intervalUp ts hleg hhalf p hp with
  | false =>
      simp only [hup, Bool.false_eq_true, ↓reduceIte] at hshift ⊢
      apply mul_left_cancel₀ hv
      calc
        v * hhe_rho h0 h' = hhe_rho h0 h' * v := mul_comm _ _
        _ = -v := hshift.symm
        _ = v * (-1) := by ring
  | true =>
      simp only [hup, ↓reduceIte] at hshift ⊢
      apply mul_left_cancel₀ hv
      calc
        v * hhe_rho h0 h' = hhe_rho h0 h' * v := mul_comm _ _
        _ = v := hshift.symm
        _ = v * 1 := by ring

theorem hlhd_intervalCore_vertices_affine (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    let raw := hlhd_intervalRaw ts p
    let up := hlhd_intervalUp ts hleg hhalf p hp
    let source := hlhc_prefixCoord ts hleg.1 p.1
    let m0 := hexInfra_midAccum hexAWStart 1 (ts.take p.1)
    let h0 := hexInfra_headAccum 1 (ts.take p.1)
    verticesAux hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp) =
      (verticesAux m0 h0 raw).map (fun z =>
        if up then z - hexAWPos source else hexAWPos source - z) := by
  dsimp only
  let raw := hlhd_intervalRaw ts p
  let up := hlhd_intervalUp ts hleg hhalf p hp
  let source := hlhc_prefixCoord ts hleg.1 p.1
  let m0 := hexInfra_midAccum hexAWStart 1 (ts.take p.1)
  let h0 := hexInfra_headAccum 1 (ts.take p.1)
  let entry := hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp)
  let h' := 1 + entry - raw.head!
  unfold hlhd_intervalCore
  rw [hlhd_coreTurns_vertices (hlhd_intervalRaw_ne ts hleg hhalf p hp)]
  change verticesAux (-halfStep h') h' raw = _
  rw [hhe_verticesAux_rigid0 h0 h' raw m0 (-halfStep h')]
  have hrho := hlhd_interval_rho ts hleg hhalf p hp
  change hhe_rho h0 h' = if up then 1 else -1 at hrho
  have hhstep := hhe_halfStep_shift h0 h' 0
  simp only [add_zero] at hhstep
  rw [hrho] at hhstep
  have hsourcePos := hlhc_prefixCoord_vertex ts hleg.1 p.1
  change m0 + halfStep h0 = hexAWPos source at hsourcePos
  apply List.map_congr_left
  intro z hz
  change hhe_rho h0 h' * (z - m0) + -halfStep h' =
    if up then z - hexAWPos source else hexAWPos source - z
  cases hup : up with
  | false =>
      simp only [hup, Bool.false_eq_true, ↓reduceIte] at hrho hhstep ⊢
      rw [hrho, hhstep, ← hsourcePos]
      ring
  | true =>
      simp only [hup, ↓reduceIte] at hrho hhstep ⊢
      rw [hrho, hhstep, ← hsourcePos]
      ring

theorem hlhd_intervalRaw_vertexPos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (r : ℕ) (hr : r ≤ (hlhd_intervalRaw ts p).length) :
    hexJordan_vertexPos
        (hexInfra_midAccum hexAWStart 1 (ts.take p.1))
        (hexInfra_headAccum 1 (ts.take p.1))
        (hlhd_intervalRaw ts p) r =
      hexJordan_vertexPos hexAWStart 1 ts (p.1 + r) := by
  have hrn : r ≤ p.2 - p.1 := by
    simpa [hlhd_intervalRaw_length ts hleg hhalf p hp] using hr
  have htake : (hlhd_intervalRaw ts p).take r =
      (ts.drop p.1).take r := by
    unfold hlhd_intervalRaw hlhr_intervalContent
    simp only [List.take_take]
    rw [min_eq_left hrn]
  unfold hexJordan_vertexPos
  rw [htake, List.take_add, hexJordan_midAccum_append,
    hexJordan_headAccum_append]

end
end StatMech.Universality
