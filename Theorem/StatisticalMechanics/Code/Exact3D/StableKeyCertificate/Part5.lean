/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part5


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

@[simp] theorem mem_stableKeyIntervalRowKeyFinset {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset rows ↔
      ∃ row, row ∈ rows ∧ row.key.toKey = k := by
  classical
  simp [stableKeyIntervalRowKeyFinset, stableKeyIntervalRowRecords,
    validRecordKeyFinset, validRecordKeyList]

end BoundedPolymerCase
end Exact3D
end StatMech
