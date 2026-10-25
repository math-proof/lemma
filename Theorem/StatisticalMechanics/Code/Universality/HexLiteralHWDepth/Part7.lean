/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part6


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_intervalLastEdge_spec (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWNeighbor (hlhc_prefixCoord ts hleg.1 (p.2 - 1))
        (hlhd_intervalLastEdge ts hleg hhalf p hp) =
      hlhc_prefixCoord ts hleg.1 p.2 := by
  unfold hlhd_intervalLastEdge
  exact Classical.choose_spec
    (hlhd_intervalLastEdge_exists ts hleg hhalf p hp)

theorem hlhd_bridge_first_edge_inward (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) {up : Bool}
    (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
    (hp2 : p.2 ≤ ts.length) (e : Fin 3)
    (he : hexAWNeighbor (hlhc_prefixCoord ts hleg.1 p.1) e =
      hlhc_prefixCoord ts hleg.1 (p.1 + 1)) :
    e = 1 ∨ e = 2 := by
  have hk : p.1 < ts.length := lt_of_lt_of_le hb.1 hp2
  have hstep := hb.2.1 (p.1 + 1) (Nat.lt_succ_self p.1)
    (Nat.succ_le_iff.mpr hb.1)
  simp only [hlhd_height, hlhd_depth] at hstep
  rw [← he] at hstep
  rcases hlhd_neighbor_depth_cases
      (hlhc_prefixCoord ts hleg.1 p.1) e with hinc | hdec | hflat
  · exact hinc.2.2
  · exact hdec.2.2
  · rw [hflat.1] at hstep
    cases up <;> simp [hlhr_signed] at hstep

theorem hlhd_intervalFirstEdge_inward (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hlhd_intervalFirstEdge ts hleg hhalf p hp = 1 ∨
      hlhd_intervalFirstEdge ts hleg hhalf p hp = 2 := by
  exact hlhd_bridge_first_edge_inward ts hleg p
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
    (hlhd_interval_index_bounds ts hleg hhalf p hp).2 _
    (hlhd_intervalFirstEdge_spec ts hleg hhalf p hp)


end
end StatMech.Universality
