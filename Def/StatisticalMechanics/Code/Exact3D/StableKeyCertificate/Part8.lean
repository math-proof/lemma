module
public import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
public import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyIntervalRow

def ExactKeySet {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (expected : Finset (StableKey maxDegree maxRange)) : Prop :=
  stableKeyIntervalRowKeyFinset rows = expected


end StableKeyIntervalRow
end BoundedPolymerCase
end Exact3D
end StatMech
