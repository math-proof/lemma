/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part34


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem minimalCubicRepresentative_class {d R maxDegree maxRange : ℕ}
    (q : CubicClass d R maxDegree maxRange) :
    cubicClass (minimalCubicRepresentative q) = q := by
  refine Quotient.inductionOn q ?_
  intro c
  apply Quotient.sound
  exact mem_cubicOrbitFiber.mp
    (Finset.min'_mem (cubicOrbitFiber c) (cubicOrbitFiber_nonempty c))


end BoundedPolymerCase
end
end Exact3D
end StatMech
