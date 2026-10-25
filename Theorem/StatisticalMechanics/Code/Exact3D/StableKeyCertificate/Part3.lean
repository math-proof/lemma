/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part3


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

@[simp] theorem validRecordKeyFinset_nil {maxDegree maxRange : ℕ} :
    validRecordKeyFinset
      ([] : List (ValidStableKeyRecord maxDegree maxRange)) = ∅ := by
  classical
  ext k
  simp [validRecordKeyFinset, validRecordKeyList]

@[simp] theorem mem_validRecordKeyFinset_cons {maxDegree maxRange : ℕ}
    (record : ValidStableKeyRecord maxDegree maxRange)
    (records : List (ValidStableKeyRecord maxDegree maxRange))
    (k : StableKey maxDegree maxRange) :
    k ∈ validRecordKeyFinset (record :: records) ↔
      record.toKey = k ∨ k ∈ validRecordKeyFinset records := by
  classical
  constructor
  · intro hk
    have hk' : k = record.toKey ∨ k ∈ validRecordKeyFinset records := by
      simpa [validRecordKeyFinset, validRecordKeyList] using hk
    rcases hk' with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · intro hk
    have hk' : k = record.toKey ∨ k ∈ validRecordKeyFinset records := by
      rcases hk with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    simpa [validRecordKeyFinset, validRecordKeyList] using hk'


end BoundedPolymerCase
end Exact3D
end StatMech
