/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part33


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem minimalCubicRepresentativeOfCase_eq_of_equivalent
    {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c') :
    minimalCubicRepresentativeOfCase c = minimalCubicRepresentativeOfCase c' := by
  simp [minimalCubicRepresentativeOfCase, cubicOrbitFiber_eq_of_equivalent h]


end BoundedPolymerCase
end
end Exact3D
end StatMech
