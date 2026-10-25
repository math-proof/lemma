/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_terminalEdge_spec (ws : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ws).IsLegalSAW) (hne : ws ≠ []) :
    hexAWNeighbor
        (hlhc_prefixCoord ws hleg.1 (ws.length - 1))
        (hlhda_terminalEdge ws hleg hne) =
      hlhc_prefixCoord ws hleg.1 ws.length := by
  unfold hlhda_terminalEdge
  have h := Classical.choose_spec
    (hlhc_prefixCoord_adjacent ws hleg (ws.length - 1)
      (Nat.sub_lt (List.length_pos_iff.mpr hne) (by omega)))
  have hpos : 1 ≤ ws.length := List.length_pos_iff.mpr hne
  simpa only [Nat.sub_add_cancel hpos] using h


end
end StatMech.Universality
