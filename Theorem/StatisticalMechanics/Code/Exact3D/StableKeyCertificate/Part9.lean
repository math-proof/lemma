/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part9


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

theorem intervalOfRows_eq_fallback_of_not_mem_keyFinset
    {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) {k : StableKey maxDegree maxRange}
    (hk : k ∉ stableKeyIntervalRowKeyFinset rows) :
    intervalOfRows rows fallback k = fallback := by
  classical
  rw [intervalOfRows, dif_neg]
  intro hex
  exact hk ((mem_stableKeyIntervalRowKeyFinset rows k).2 hex)

theorem exists_row_intervalOfRows_eq_of_mem_keyFinset
    {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) {k : StableKey maxDegree maxRange}
    (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
    ∃ row, row ∈ rows ∧ row.key.toKey = k ∧
      intervalOfRows rows fallback k = row.interval := by
  classical
  have hex : ∃ row, row ∈ rows ∧ row.key.toKey = k :=
    (mem_stableKeyIntervalRowKeyFinset rows k).mp hk
  refine ⟨Classical.choose hex, ?_, ?_, ?_⟩
  · exact (Classical.choose_spec hex).1
  · exact (Classical.choose_spec hex).2
  · rw [intervalOfRows, dif_pos hex]

theorem intervalOfRows_memR_of_mem_keyFinset {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) (keyValue : StableKey maxDegree maxRange → ℝ)
    (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey))
    {k : StableKey maxDegree maxRange}
    (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
    (intervalOfRows rows fallback k).MemR (keyValue k) := by
  classical
  have hex : ∃ row, row ∈ rows ∧ row.key.toKey = k :=
    (mem_stableKeyIntervalRowKeyFinset rows k).mp hk
  rw [intervalOfRows, dif_pos hex]
  have hspec := Classical.choose_spec hex
  simpa [hspec.2] using hrow (Classical.choose hex) hspec.1


end BoundedPolymerCase
end Exact3D
end StatMech
