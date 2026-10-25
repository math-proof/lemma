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
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeFull.Part3


namespace StatMech.Universality

open List

open HexWalk


def hxb_LegalRungs (γ : List (ℕ × ℤ)) : Prop := ∀ p ∈ γ, p.2 = 1 ∨ p.2 = -1


def hxb_LegalContents (bs : List HexBridge) : Prop :=
  ∀ b ∈ bs, ∀ t ∈ b.content, t = 1 ∨ t = -1


end StatMech.Universality
