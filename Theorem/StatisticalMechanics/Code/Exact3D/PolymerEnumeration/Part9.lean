/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part11


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem classifyBoundedLocalCoordinate_degree_val
    {d R maxDegree maxRange : ℕ}
    (c : BoundedLocalCoordinate d R maxDegree maxRange) :
    ((classifyBoundedLocalCoordinate c).degree : ℕ) = c.1.degree :=
  rfl


@[simp] theorem classifyBoundedLocalCoordinate_range_val
    {d R maxDegree maxRange : ℕ}
    (c : BoundedLocalCoordinate d R maxDegree maxRange) :
    ((classifyBoundedLocalCoordinate c).range : ℕ) = c.1.range :=
  rfl


end BoundedPolymerCase
end
end Exact3D
end StatMech
