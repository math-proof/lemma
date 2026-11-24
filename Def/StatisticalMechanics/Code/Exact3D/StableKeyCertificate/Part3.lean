module
public import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
public import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part2


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

def validRecordKeyList {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange)) :
    List (StableKey maxDegree maxRange) :=
  records.map ValidStableKeyRecord.toKey


def validRecordKeyFinset {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange)) :
    Finset (StableKey maxDegree maxRange) :=
  (validRecordKeyList records).toFinset

end BoundedPolymerCase
end Exact3D
end StatMech
