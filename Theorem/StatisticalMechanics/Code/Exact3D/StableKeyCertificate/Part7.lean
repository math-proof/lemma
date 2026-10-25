/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part7


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyIntervalRow

theorem mem_keyFinset_map_ofKeyInterval {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset
        (s.toList.map (ofKeyInterval intervalOf)) ↔
      k ∈ s := by
  classical
  simp [stableKeyIntervalRowKeyFinset, stableKeyIntervalRowRecords,
    validRecordKeyFinset, validRecordKeyList, ofKeyInterval]

@[simp] theorem mem_keyFinset_rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset (rowsOfKeys s intervalOf) ↔
      k ∈ s := by
  simpa [rowsOfKeys, ofKey] using
    mem_keyFinset_map_ofKeyInterval s intervalOf k


theorem interval_eq_of_mem_map_ofKeyInterval {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ s.toList.map (ofKeyInterval intervalOf)) :
    row.interval = intervalOf row.key.toKey := by
  rcases List.mem_map.mp hrow with ⟨k, _hk, rfl⟩
  simp [ofKeyInterval]


theorem interval_eq_of_mem_rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ rowsOfKeys s intervalOf) :
    row.interval = intervalOf row.key.toKey := by
  exact interval_eq_of_mem_map_ofKeyInterval s intervalOf
    (by simpa [rowsOfKeys, ofKey] using hrow)


theorem memR_of_mem_map_ofKeyInterval {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hmem :
      ∀ k, k ∈ s → (intervalOf k).MemR (keyValue k))
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ s.toList.map (ofKeyInterval intervalOf)) :
    row.interval.MemR (keyValue row.key.toKey) := by
  classical
  rcases List.mem_map.mp hrow with ⟨k, hk, rfl⟩
  simpa [ofKeyInterval] using hmem k (by simpa using hk)


theorem memR_of_mem_rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hmem :
      ∀ k, k ∈ s → (intervalOf k).MemR (keyValue k))
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ rowsOfKeys s intervalOf) :
    row.interval.MemR (keyValue row.key.toKey) :=
  memR_of_mem_map_ofKeyInterval s intervalOf keyValue hmem
    (by simpa [rowsOfKeys, ofKey] using hrow)


theorem upper_le_of_mem_map_ofKeyInterval {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    {bound : ℝ}
    (hupper :
      ∀ k, k ∈ s → (((intervalOf k).upper : ℚ) : ℝ) ≤ bound)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ s.toList.map (ofKeyInterval intervalOf)) :
    ((row.interval.upper : ℚ) : ℝ) ≤ bound := by
  classical
  rcases List.mem_map.mp hrow with ⟨k, hk, rfl⟩
  simpa [ofKeyInterval] using hupper k (by simpa using hk)


theorem upper_le_of_mem_rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    {bound : ℝ}
    (hupper :
      ∀ k, k ∈ s → (((intervalOf k).upper : ℚ) : ℝ) ≤ bound)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ rowsOfKeys s intervalOf) :
    ((row.interval.upper : ℚ) : ℝ) ≤ bound :=
  upper_le_of_mem_map_ofKeyInterval s intervalOf hupper
    (by simpa [rowsOfKeys, ofKey] using hrow)


end StableKeyIntervalRow
end BoundedPolymerCase
end Exact3D
end StatMech
