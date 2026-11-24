module
public import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
public import Theorem.StatisticalMechanics.Code.Universality.HexHWBridgeSubsetBound


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


noncomputable def hhs_activeBridges
    (S : Finset HexHWContentHalf) : Finset HexBridge := by
  classical
  exact S.biUnion (fun s => s.1.toFinset)

end StatMech.Universality
