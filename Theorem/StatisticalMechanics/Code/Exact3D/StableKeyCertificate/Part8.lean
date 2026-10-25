/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part8


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyIntervalRow

theorem exactKeySet_map_ofKeyInterval {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    ExactKeySet (s.toList.map (ofKeyInterval intervalOf)) s := by
  classical
  ext k
  exact mem_keyFinset_map_ofKeyInterval s intervalOf k


theorem exactKeySet_rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    ExactKeySet (rowsOfKeys s intervalOf) s := by
  classical
  ext k
  exact mem_keyFinset_rowsOfKeys s intervalOf k

theorem exactKeySet_iff {maxDegree maxRange : ℕ}
    {rows : List (StableKeyIntervalRow maxDegree maxRange)}
    {expected : Finset (StableKey maxDegree maxRange)} :
    ExactKeySet rows expected ↔
      ∀ k, k ∈ stableKeyIntervalRowKeyFinset rows ↔ k ∈ expected := by
  classical
  constructor
  · intro h k
    change stableKeyIntervalRowKeyFinset rows = expected at h
    rw [h]
  · intro h
    ext k
    exact h k


theorem mem_expected_of_exactKeySet {maxDegree maxRange : ℕ}
    {rows : List (StableKeyIntervalRow maxDegree maxRange)}
    {expected : Finset (StableKey maxDegree maxRange)}
    (h : ExactKeySet rows expected)
    {k : StableKey maxDegree maxRange}
    (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
    k ∈ expected := by
  change stableKeyIntervalRowKeyFinset rows = expected at h
  rwa [h] at hk


theorem mem_rows_of_exactKeySet {maxDegree maxRange : ℕ}
    {rows : List (StableKeyIntervalRow maxDegree maxRange)}
    {expected : Finset (StableKey maxDegree maxRange)}
    (h : ExactKeySet rows expected)
    {k : StableKey maxDegree maxRange}
    (hk : k ∈ expected) :
    k ∈ stableKeyIntervalRowKeyFinset rows := by
  change stableKeyIntervalRowKeyFinset rows = expected at h
  rw [h]
  exact hk


theorem row_key_mem_expected_of_exactKeySet {maxDegree maxRange : ℕ}
    {rows : List (StableKeyIntervalRow maxDegree maxRange)}
    {expected : Finset (StableKey maxDegree maxRange)}
    (h : ExactKeySet rows expected)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ rows) :
    row.key.toKey ∈ expected := by
  exact mem_expected_of_exactKeySet h
    ((mem_stableKeyIntervalRowKeyFinset rows row.key.toKey).2
      ⟨row, hrow, rfl⟩)


theorem classifier_mem_rows_of_exactKeySet {α : Type*}
    {maxDegree maxRange : ℕ}
    {rows : List (StableKeyIntervalRow maxDegree maxRange)}
    {expected : Finset (StableKey maxDegree maxRange)}
    (h : ExactKeySet rows expected)
    (classifier : α → StableKey maxDegree maxRange)
    (hclassifier : ∀ a, classifier a ∈ expected)
    (a : α) :
    classifier a ∈ stableKeyIntervalRowKeyFinset rows :=
  mem_rows_of_exactKeySet h (hclassifier a)

end StableKeyIntervalRow

@[simp] theorem stableKeyIntervalRowKeyFinset_nil {maxDegree maxRange : ℕ} :
    stableKeyIntervalRowKeyFinset
      ([] : List (StableKeyIntervalRow maxDegree maxRange)) = ∅ := by
  classical
  ext k
  simp

@[simp] theorem mem_stableKeyIntervalRowKeyFinset_cons
    {maxDegree maxRange : ℕ}
    (row : StableKeyIntervalRow maxDegree maxRange)
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset (row :: rows) ↔
      row.key.toKey = k ∨ k ∈ stableKeyIntervalRowKeyFinset rows := by
  classical
  simp


end BoundedPolymerCase
end Exact3D
end StatMech
