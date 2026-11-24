module
public import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackage
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
public import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part3
public import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
public import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace InfiniteTailStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


theorem mem_rowKeyFinset_map_zeroOneRowOfKey {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset (s.toList.map zeroOneRowOfKey) ↔
      k ∈ s := by
  classical
  simpa [zeroOneRowOfKey] using
    StableKeyIntervalRow.mem_keyFinset_map_ofKeyInterval
      s (fun _ => zeroOneInterval) k


end InfiniteTailStableKeyPackageExample
end Exact3D
end StatMech
