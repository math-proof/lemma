/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Instance.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part7


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

def coordinateReflectionClass {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    CoordinateReflectionClass d R maxDegree maxRange :=
  Quotient.mk (coordinateReflectionSetoid d R maxDegree maxRange) c


noncomputable def exhaustiveCoordinateReflectionClassTable
    (d R maxDegree maxRange : ℕ) :
    Finset (CoordinateReflectionClass d R maxDegree maxRange) :=
  Finset.univ


end BoundedPolymerCase
end
end Exact3D
end StatMech
