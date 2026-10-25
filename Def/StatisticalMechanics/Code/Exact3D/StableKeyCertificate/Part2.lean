/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Structure.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part2


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace ValidStableKeyRecord

def toKey {maxDegree maxRange : ℕ}
    (r : ValidStableKeyRecord maxDegree maxRange) : StableKey maxDegree maxRange :=
  r.record.toKey r.degree_le r.range_le


def ofKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    ValidStableKeyRecord maxDegree maxRange where
  record := StableKeyRecord.ofKey k
  degree_le := StableKeyRecord.ofKey_degree_le k
  range_le := StableKeyRecord.ofKey_range_le k

end ValidStableKeyRecord
end BoundedPolymerCase
end Exact3D
end StatMech
