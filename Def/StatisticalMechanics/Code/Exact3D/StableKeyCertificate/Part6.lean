/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part5


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyIntervalRow

def ofKeyInterval {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    StableKeyIntervalRow maxDegree maxRange where
  key := ValidStableKeyRecord.ofKey k
  interval := intervalOf k


def ofKey {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    StableKeyIntervalRow maxDegree maxRange :=
  ofKeyInterval intervalOf k

end StableKeyIntervalRow
end BoundedPolymerCase
end Exact3D
end StatMech
