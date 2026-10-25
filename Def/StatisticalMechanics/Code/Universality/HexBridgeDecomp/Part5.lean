/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part4


namespace StatMech.Universality

open List


def hexHW_WF (γ : List (ℕ × ℤ)) : Prop := ∀ p ∈ γ, 0 < p.1

end StatMech.Universality
