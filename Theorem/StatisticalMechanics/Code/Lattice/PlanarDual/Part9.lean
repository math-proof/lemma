/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.PlanarDual.Part9
open SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem crossEdge_mk (x y : Site 2) :
    crossEdge s(x, y) = s(rot90Fun x, rot90Fun y) := by simp [crossEdge]


end Lattice
end StatMech
