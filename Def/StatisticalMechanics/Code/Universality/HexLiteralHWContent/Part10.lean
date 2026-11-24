module
public import Mathlib
public import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
public import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part9


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


noncomputable def hhc_literalLower (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) : HexHWContentHalf :=
  hhc_halfOfList (d.1.take (hexW2_cutPos h0 d.1))


noncomputable def hhc_literalUpper (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) : HexHWContentHalf :=
  hhc_halfOfList (d.1.drop (hexW2_cutPos h0 d.1))

end StatMech.Universality
