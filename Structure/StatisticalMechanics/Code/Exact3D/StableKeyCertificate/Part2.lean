/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

structure ValidStableKeyRecord (maxDegree maxRange : ℕ) where
  record : StableKeyRecord
  degree_le : record.degree ≤ maxDegree
  range_le : record.range ≤ maxRange

end BoundedPolymerCase
end Exact3D
end StatMech
