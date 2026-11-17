/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
public import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part3


public section

namespace StatMech.Universality

open HexWalk

open scoped BigOperators


structure HexHWContentDecomp (D : Type) where
  
  turns : D → List ℤ
  
  turns_inj : Function.Injective turns
  
  lower : D → HexHWContentHalf
  
  upper : D → HexHWContentHalf
  
  reconstruct : ∀ d, turns d = hhc_halfTurns (lower d) ++ hhc_halfTurns (upper d)

end StatMech.Universality
