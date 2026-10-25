/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Def.StatisticalMechanics.Code.Universality.HexBridgeFull


namespace StatMech.Universality

open List

open HexWalk


@[simp]
theorem hxb_rungTurns_nil : hxb_rungTurns [] = [] := rfl


@[simp]
theorem hxb_rungTurns_append (γ δ : List (ℕ × ℤ)) :
    hxb_rungTurns (γ ++ δ) = hxb_rungTurns γ ++ hxb_rungTurns δ := by
  simp [hxb_rungTurns]


@[simp]
theorem hxb_rungTurns_rungs (b : HexBridge) : hxb_rungTurns b.rungs = b.content := by
  simp [hxb_rungTurns, HexBridge.rungs, List.map_map]


end StatMech.Universality
