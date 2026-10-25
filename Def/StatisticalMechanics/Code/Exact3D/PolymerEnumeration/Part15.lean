/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part12


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

noncomputable def reflectLocalCoordinate {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    LocalPolymerCoordinate d where
  support := c.support.reflectCoordinates ε
  degree := c.degree
  range := c.range
  symmetry := c.symmetry

end BoundedPolymerCase
end
end Exact3D
end StatMech
