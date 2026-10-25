/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificate


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyRecord

theorem ofKey_degree_le {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    (ofKey k).degree ≤ maxDegree := by
  dsimp [ofKey]
  exact Nat.le_of_lt_succ (ofLex (ofLex k).2).1.2

theorem ofKey_range_le {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    (ofKey k).range ≤ maxRange := by
  dsimp [ofKey]
  exact Nat.le_of_lt_succ (ofLex (ofLex k).2).2.2

@[simp] theorem ofKey_stableKey_support {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    (ofKey (stableKey c)).support = supportKey c.support := by
  simp [ofKey, stableKey]

@[simp] theorem ofKey_stableKey_degree {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    (ofKey (stableKey c)).degree = c.degree := by
  simp [ofKey, stableKey]

@[simp] theorem ofKey_stableKey_range {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    (ofKey (stableKey c)).range = c.range := by
  simp [ofKey, stableKey]

@[simp] theorem toKey_ofKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    (ofKey k).toKey (ofKey_degree_le k) (ofKey_range_le k) = k := by
  simp [toKey, ofKey]

@[simp] theorem ofKey_toKey {maxDegree maxRange : ℕ} (r : StableKeyRecord)
    (hdegree : r.degree ≤ maxDegree) (hrange : r.range ≤ maxRange) :
    ofKey (r.toKey hdegree hrange) = r := by
  cases r
  simp [toKey, ofKey]

end StableKeyRecord
end BoundedPolymerCase
end Exact3D
end StatMech
