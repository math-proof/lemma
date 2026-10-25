/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part6


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyIntervalRow

@[simp] theorem ofKeyInterval_key_toKey {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    (ofKeyInterval intervalOf k).key.toKey = k := by
  simp [ofKeyInterval]

@[simp] theorem ofKeyInterval_interval {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    (ofKeyInterval intervalOf k).interval = intervalOf k :=
  rfl

@[simp] theorem ofKey_key_toKey {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    (ofKey intervalOf k).key.toKey = k := by
  simp [ofKey]

@[simp] theorem ofKey_interval {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    (ofKey intervalOf k).interval = intervalOf k :=
  rfl


end StableKeyIntervalRow
end BoundedPolymerCase
end Exact3D
end StatMech
