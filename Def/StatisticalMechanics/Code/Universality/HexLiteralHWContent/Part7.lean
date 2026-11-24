module
public import Mathlib
public import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
public import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

open scoped BigOperators


noncomputable def hhc_literalDecomp (a : ℂ) (h0 : ℤ) (N : ℕ)
    (lower upper : hhc_Dn a h0 N → HexHWContentHalf)
    (hreconstruct : ∀ d, d.1 = hhc_halfTurns (lower d) ++ hhc_halfTurns (upper d)) :
    HexHWContentDecomp (hhc_Dn a h0 N) where
  turns := Subtype.val
  turns_inj := Subtype.val_injective
  lower := lower
  upper := upper
  reconstruct := hreconstruct


end StatMech.Universality
