/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable


public section

namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


structure HexW2SBridge where
  
  head : ℤ
  
  turns : List ℤ


end StatMech.Universality
