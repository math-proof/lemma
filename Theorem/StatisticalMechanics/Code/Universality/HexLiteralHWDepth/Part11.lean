/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part10


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_entryTurn_legal (e : Fin 3) :
    hlhd_entryTurn e = 1 ∨ hlhd_entryTurn e = -1 := by
  unfold hlhd_entryTurn
  split <;> simp

theorem hlhd_entryTurn_heading {e : Fin 3} (he : e = 1 ∨ e = 2) :
    1 + hlhd_entryTurn e = hexAWHeading hexAWOriginCoord e := by
  rcases he with rfl | rfl <;>
    simp [hlhd_entryTurn, hexAWHeading, hexAWOriginCoord]


end
end StatMech.Universality
