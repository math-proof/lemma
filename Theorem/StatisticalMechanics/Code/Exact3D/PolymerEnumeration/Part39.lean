/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part45


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem coarseIntervalTable_covers (d R maxDegree maxRange : ℕ) :
    RatInterval.CaseTable.Covers
      (coarseIntervalTable d R maxDegree maxRange) id := by
  intro c
  exact exhaustiveTable_covers d R maxDegree maxRange c


theorem coarseIntervalTable_sound_of_abs_le_one {d R maxDegree maxRange : ℕ}
    (value : BoundedPolymerCase d R maxDegree maxRange → ℝ)
    (hvalue : ∀ c, |value c| ≤ 1) :
    RatInterval.CaseTable.Sound
      (coarseIntervalTable d R maxDegree maxRange) id value := by
  intro c
  have h := hvalue c
  rw [abs_le] at h
  simpa [coarseIntervalTable, RatInterval.MemR] using h

end BoundedPolymerCase
end
end Exact3D
end StatMech
