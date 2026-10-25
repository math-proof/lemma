/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part38


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

noncomputable def coarseIntervalTable (d R maxDegree maxRange : ℕ) :
    RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange) where
  cases := exhaustiveTable d R maxDegree maxRange
  interval := fun _ =>
    { lower := -1
      upper := 1
      lower_le_upper := by norm_num }


end BoundedPolymerCase
end
end Exact3D
end StatMech
