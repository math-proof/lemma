module
public import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
public import Theorem.StatisticalMechanics.Code.Universality.HexHWBridgeSubsetBound.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open scoped BigOperators


noncomputable def hhs_bridgeEncoding
    (S : Finset HexHWContentHalf) (s : HexHWContentHalf) :
    ∀ b, b ∈ hhs_activeBridges S → Bool := by
  classical
  exact fun b _ => decide (b ∈ s.1)

end StatMech.Universality
