/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Abbrev.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part3


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

noncomputable def classifyBoundedLocalCoordinate {d R maxDegree maxRange : ℕ}
    (c : BoundedLocalCoordinate d R maxDegree maxRange) :
    BoundedPolymerCase d R maxDegree maxRange :=
  ofLocalCoordinate c.1 c.2.1 c.2.2.1 c.2.2.2


end BoundedPolymerCase
end
end Exact3D
end StatMech
