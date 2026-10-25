/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part8


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

noncomputable def intervalOfRows {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) (k : StableKey maxDegree maxRange) : RatInterval :=
  if h : ∃ row, row ∈ rows ∧ row.key.toKey = k then
    h.choose.interval
  else
    fallback

end BoundedPolymerCase
end Exact3D
end StatMech
