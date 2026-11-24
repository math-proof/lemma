module
public import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
public import Def.StatisticalMechanics.Code.Universality.HexHWBridgeSubsetBound


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


theorem hhs_mem_activeBridges
    {S : Finset HexHWContentHalf} {s : HexHWContentHalf}
    (hs : s ∈ S) {b : HexBridge} (hb : b ∈ s.1) :
    b ∈ hhs_activeBridges S := by
  classical
  rw [hhs_activeBridges, Finset.mem_biUnion]
  exact ⟨s, hs, List.mem_toFinset.mpr hb⟩

end StatMech.Universality
