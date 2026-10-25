/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part10
import Def.StatisticalMechanics.Code.Exact3D.StableKeyCertificateExample


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyCertificateExample

open StatMech.Lattice


theorem rowOfKey_memR_zero {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    (rowOfKey k).interval.MemR (0 : ℝ) := by
  simp [rowOfKey, zeroInterval, RatInterval.point, RatInterval.MemR]


theorem mem_rowKeyFinset_map_rowOfKey {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset (s.toList.map rowOfKey) ↔ k ∈ s := by
  classical
  simpa [rowOfKey] using
    StableKeyIntervalRow.mem_keyFinset_map_ofKeyInterval
      s (fun _ => zeroInterval) k


end StableKeyCertificateExample
end BoundedPolymerCase
end Exact3D
end StatMech
