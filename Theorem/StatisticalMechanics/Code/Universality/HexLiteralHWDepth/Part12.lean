/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part11


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_exitTurn_legal (e : Fin 3) :
    hlhd_exitTurn e = 1 ∨ hlhd_exitTurn e = -1 := by
  unfold hlhd_exitTurn
  split <;> simp

theorem hlhd_exitTurn_heading {e : Fin 3} (he : e = 1 ∨ e = 2) :
    hexAWHeading (HexAWCoord.mk 0 0 .black) e + hlhd_exitTurn e = 1 := by
  rcases he with rfl | rfl <;>
    simp [hlhd_exitTurn, hexAWHeading]


end
end StatMech.Universality
