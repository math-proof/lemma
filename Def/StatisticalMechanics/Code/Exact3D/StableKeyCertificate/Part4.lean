/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part3


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

noncomputable def externalStableKeyIntervalTable {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable (StableKey maxDegree maxRange) where
  cases := validRecordKeyFinset records
  interval := intervalOf

end BoundedPolymerCase
end Exact3D
end StatMech
