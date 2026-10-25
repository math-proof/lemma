/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Structure.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part3


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

def stableKeyIntervalRowRecords {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange)) :
    List (ValidStableKeyRecord maxDegree maxRange) :=
  rows.map StableKeyIntervalRow.key


def stableKeyIntervalRowKeyFinset {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange)) :
    Finset (StableKey maxDegree maxRange) :=
  validRecordKeyFinset (stableKeyIntervalRowRecords rows)

end BoundedPolymerCase
end Exact3D
end StatMech
