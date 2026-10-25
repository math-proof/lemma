/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part5


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_intervalFirstEdge_spec (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWNeighbor (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhd_intervalFirstEdge ts hleg hhalf p hp) =
      hlhc_prefixCoord ts hleg.1 (p.1 + 1) := by
  unfold hlhd_intervalFirstEdge
  exact Classical.choose_spec (hlhc_prefixCoord_adjacent ts hleg p.1
    (lt_of_lt_of_le (hlhd_interval_index_bounds ts hleg hhalf p hp).1
      (hlhd_interval_index_bounds ts hleg hhalf p hp).2))

theorem hlhd_intervalLastEdge_exists (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    ∃ e : Fin 3,
      hexAWNeighbor (hlhc_prefixCoord ts hleg.1 (p.2 - 1)) e =
        hlhc_prefixCoord ts hleg.1 p.2 := by
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent ts hleg (p.2 - 1)
    (by omega)
  refine ⟨e, ?_⟩
  have hp2pos : 0 < p.2 := lt_of_le_of_lt (Nat.zero_le p.1) hb.1
  have hp2one : 1 ≤ p.2 := hp2pos
  simpa only [Nat.sub_add_cancel hp2one] using he

end
end StatMech.Universality
