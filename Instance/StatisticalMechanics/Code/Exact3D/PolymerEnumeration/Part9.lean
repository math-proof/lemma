/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part23


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

instance instCubicEquivalentDecidableRel (d R maxDegree maxRange : ℕ) :
    DecidableRel (@cubicEquivalent d R maxDegree maxRange) := fun c c' =>
  decidable_of_iff (finiteCubicEquivalent c c')
    (finiteCubicEquivalent_iff c c')


end BoundedPolymerCase
end
end Exact3D
end StatMech
