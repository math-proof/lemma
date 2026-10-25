/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part5


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhd_intervalFirstEdge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : Fin 3 := by
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  exact Classical.choose (hlhc_prefixCoord_adjacent ts hleg p.1
    (lt_of_lt_of_le hb.1 hb.2))

end
end StatMech.Universality
