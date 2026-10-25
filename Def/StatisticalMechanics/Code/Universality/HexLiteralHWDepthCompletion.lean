/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhda_terminalEdge (ws : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ws).IsLegalSAW) (hne : ws ≠ []) : Fin 3 :=
  Classical.choose (hlhc_prefixCoord_adjacent ws hleg (ws.length - 1)
    (Nat.sub_lt (List.length_pos_iff.mpr hne) (by omega)))

end
end StatMech.Universality
