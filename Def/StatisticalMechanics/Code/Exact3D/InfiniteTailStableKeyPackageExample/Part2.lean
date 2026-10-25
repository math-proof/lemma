/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackage
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part3
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailStableKeyPackageExample

open BoundedPolymerCase

open BoundedPolymerCase.StableKeyCertificateExample

open BoundedPolymerCase.StableKeyTailBridgeExample

open BoundedPolymerCase.GeneratedTableTailBridgeExample

open InfiniteTailTableWitnessPackage


noncomputable def rawZeroOneRows (d R maxDegree maxRange : ℕ) :
    List (StableKeyIntervalRow maxDegree maxRange) :=
  StableKeyIntervalRow.rowsOfKeys
    ((exhaustiveTable d R maxDegree maxRange).image stableKey)
    (fun _ => zeroOneInterval)


noncomputable def minimalCubicZeroOneRows (d R maxDegree maxRange : ℕ) :
    List (StableKeyIntervalRow maxDegree maxRange) :=
  StableKeyIntervalRow.rowsOfKeys
    ((exhaustiveCubicClassTable d R maxDegree maxRange).image
      minimalCubicStableKey)
    (fun _ => zeroOneInterval)


end InfiniteTailStableKeyPackageExample
end Exact3D
end StatMech
