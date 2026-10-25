/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part6


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyIntervalRow

noncomputable def rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    List (StableKeyIntervalRow maxDegree maxRange) :=
  s.toList.map (ofKey intervalOf)


end StableKeyIntervalRow
end BoundedPolymerCase
end Exact3D
end StatMech
