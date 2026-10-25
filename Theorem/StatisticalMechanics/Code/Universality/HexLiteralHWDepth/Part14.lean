/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part12


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_bitTurn_turnBit {t : ℤ} (ht : t = 1 ∨ t = -1) :
    hlhd_bitTurn (hlhd_turnBit t) = t := by
  rcases ht with rfl | rfl <;>
    simp [hlhd_bitTurn, hlhd_turnBit]


end
end StatMech.Universality
