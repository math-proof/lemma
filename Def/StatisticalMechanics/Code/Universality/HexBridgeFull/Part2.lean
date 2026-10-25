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
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeFull


namespace StatMech.Universality

open List

open HexWalk


noncomputable def hxb_walkOf (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ)) : HexWalk :=
  ofTurns a h0 (hxb_rungTurns γ)

end StatMech.Universality
