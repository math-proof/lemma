/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part19


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_normalized_depth_bounds (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) {up : Bool}
    (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
    {k : ℕ} (hklo : p.1 ≤ k) (hkhi : k ≤ p.2) :
    0 ≤ hexAWDepth (hlhd_normalizeCoord up
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 k)) ∧
      hexAWDepth (hlhd_normalizeCoord up
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 k)) ≤
          (hlhd_width ts hleg p : ℤ) := by
  have hbounds := hlhd_bridge_depth_bounds ts hleg p hb hklo hkhi
  have hend := hb.2.1 p.2 hb.1 le_rfl
  unfold hlhd_width hlhd_delta
  rw [hlhd_normalizeCoord_depth]
  cases up with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, hlhr_signed,
        hlhd_height, hlhd_depth] at hbounds hend ⊢
      have hksourceR :
          (hexAWDepth (hlhc_prefixCoord ts hleg.1 k) : ℝ) ≤
            hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        linarith [hbounds.1]
      have hendkR :
          (hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) : ℝ) ≤
            hexAWDepth (hlhc_prefixCoord ts hleg.1 k) := by
        linarith [hbounds.2]
      have hendR :
          (hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) : ℝ) <
            hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        linarith
      have hksource : hexAWDepth (hlhc_prefixCoord ts hleg.1 k) ≤
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        exact_mod_cast hksourceR
      have hendk : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) ≤
          hexAWDepth (hlhc_prefixCoord ts hleg.1 k) := by
        exact_mod_cast hendkR
      have hendZ : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        exact_mod_cast hendR
      rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  | true =>
      simp only [↓reduceIte, hlhr_signed, hlhd_height, hlhd_depth] at hbounds hend ⊢
      have hsourcek : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) ≤
          hexAWDepth (hlhc_prefixCoord ts hleg.1 k) := by
        exact_mod_cast hbounds.1
      have hkend : hexAWDepth (hlhc_prefixCoord ts hleg.1 k) ≤
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) := by
        exact_mod_cast hbounds.2
      have hendZ : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) := by
        exact_mod_cast hend
      rw [Int.natAbs_of_nonneg (by omega)]
      omega


theorem hlhd_normalized_depth_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) {up : Bool}
    (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
    {k : ℕ} (hklo : p.1 < k) (hkhi : k ≤ p.2) :
    0 < hexAWDepth (hlhd_normalizeCoord up
      (hlhc_prefixCoord ts hleg.1 p.1)
      (hlhc_prefixCoord ts hleg.1 k)) := by
  have hstrict := hb.2.1 k hklo hkhi
  rw [hlhd_normalizeCoord_depth]
  cases up with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, hlhr_signed,
        hlhd_height, hlhd_depth] at hstrict ⊢
      have hz : hexAWDepth (hlhc_prefixCoord ts hleg.1 k) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        exact_mod_cast (show
          (hexAWDepth (hlhc_prefixCoord ts hleg.1 k) : ℝ) <
            hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) by linarith)
      omega
  | true =>
      simp only [↓reduceIte, hlhr_signed, hlhd_height,
        hlhd_depth] at hstrict ⊢
      have hz : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 k) := by
        exact_mod_cast hstrict
      omega

theorem hlhd_normalized_endpoint_depth (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) {up : Bool}
    (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p) :
    hexAWDepth (hlhd_normalizeCoord up
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 p.2)) =
      hlhd_width ts hleg p := by
  have hend := hb.2.1 p.2 hb.1 le_rfl
  unfold hlhd_width hlhd_delta
  rw [hlhd_normalizeCoord_depth]
  cases up with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, hlhr_signed,
        hlhd_height, hlhd_depth] at hend ⊢
      have hendR :
          (hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) : ℝ) <
            hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        linarith
      have hendZ : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        exact_mod_cast hendR
      rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  | true =>
      simp only [↓reduceIte, hlhr_signed, hlhd_height, hlhd_depth] at hend ⊢
      have hendZ : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) := by
        exact_mod_cast hend
      rw [Int.natAbs_of_nonneg (by omega)]

theorem hlhd_intervalFarCoord_depth (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWDepth (hlhd_intervalFarCoord ts hleg hhalf p hp) =
      hlhd_width ts hleg p := by
  exact hlhd_normalized_endpoint_depth ts hleg p
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)

theorem hlhd_intervalPrevCoord_depth_le (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWDepth (hlhd_intervalPrevCoord ts hleg hhalf p hp) ≤
      hexAWDepth (hlhd_intervalFarCoord ts hleg hhalf p hp) := by
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  have hprev := hlhd_normalized_depth_bounds ts hleg p
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
    (k := p.2 - 1) (by omega) (by omega)
  rw [hlhd_intervalFarCoord_depth ts hleg hhalf p hp]
  exact hprev.2

theorem hlhd_intervalLastEdge_zero_of_far_black (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (hblack : (hlhd_intervalFarCoord ts hleg hhalf p hp).color = .black) :
    hlhd_intervalLastEdge ts hleg hhalf p hp = 0 := by
  exact hlhd_neighbor_black_max_edge_zero _ _ _
    (hlhd_intervalLastEdge_normalized ts hleg hhalf p hp) hblack
    (hlhd_intervalPrevCoord_depth_le ts hleg hhalf p hp)

end
end StatMech.Universality
