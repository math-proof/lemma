/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part2


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace ValidStableKeyRecord

@[simp] theorem toKey_mk {maxDegree maxRange : ℕ}
    (record : StableKeyRecord) (degree_le : record.degree ≤ maxDegree)
    (range_le : record.range ≤ maxRange) :
    toKey (ValidStableKeyRecord.mk record degree_le range_le) =
      record.toKey degree_le range_le :=
  rfl

@[simp] theorem toKey_ofKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    (ofKey k).toKey = k := by
  simp [ofKey, toKey]

end ValidStableKeyRecord
end BoundedPolymerCase
end Exact3D
end StatMech
