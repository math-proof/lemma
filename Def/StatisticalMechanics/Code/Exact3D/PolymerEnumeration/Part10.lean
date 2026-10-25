/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part7


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

noncomputable def ofLocalCoordinate {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    BoundedPolymerCase d R maxDegree maxRange where
  support := boundedSupportOf c.support hbox
  degree := ⟨c.degree, Nat.lt_succ_of_le hdegree⟩
  range := ⟨c.range, Nat.lt_succ_of_le hrange⟩


end BoundedPolymerCase
end
end Exact3D
end StatMech
