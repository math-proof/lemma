/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexHWBridgeSubsetBound.Part3


namespace StatMech.Universality

open scoped BigOperators


def hhs_boolWeight (x : ℝ) (b : HexBridge) (q : Bool) : ℝ :=
  if q then hhc_bridgeWeight x b else 1

end StatMech.Universality
