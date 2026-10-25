/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Structure.StatisticalMechanics.Code.Universality.HexW2Summable


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


noncomputable def hexW2S_bridgeWt (x : ℝ) (b : HexW2SBridge) : ℝ :=
  hexSAWwt 0 b.head x b.turns


end StatMech.Universality
