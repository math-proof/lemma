/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part4


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

@[simp] theorem externalStableKeyIntervalTable_cases {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    (externalStableKeyIntervalTable records intervalOf).cases =
      validRecordKeyFinset records :=
  rfl

@[simp] theorem externalStableKeyIntervalTable_interval
    {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    (externalStableKeyIntervalTable records intervalOf).interval k =
      intervalOf k :=
  rfl


theorem externalStableKeyIntervalTable_covers_and_sound_of_keyValue
    {α : Type*} {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (classifier : α → StableKey maxDegree maxRange)
    (value : α → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hcover : ∀ a, classifier a ∈ validRecordKeyFinset records)
    (hvalue : ∀ a, value a = keyValue (classifier a))
    (hkey : ∀ k, k ∈ validRecordKeyFinset records →
      (intervalOf k).MemR (keyValue k)) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalTable records intervalOf) classifier ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalTable records intervalOf) classifier value := by
  constructor
  · intro a
    exact hcover a
  · intro a
    rw [hvalue a]
    exact hkey (classifier a) (hcover a)


end BoundedPolymerCase
end Exact3D
end StatMech
