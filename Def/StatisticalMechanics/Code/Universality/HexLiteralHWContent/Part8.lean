module
public import Mathlib
public import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
public import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part7


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


def hhc_bridgeOfNonempty (ts : List ℤ) (hne : ts ≠ []) : HexBridge where
  width := ts.length
  width_pos := List.length_pos_iff.mpr hne
  content := ts
  content_ne := hne

end StatMech.Universality
