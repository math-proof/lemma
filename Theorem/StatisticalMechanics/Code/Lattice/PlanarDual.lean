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
import Def.StatisticalMechanics.Code.Lattice.PlanarDual
open SimpleGraph


namespace StatMech

namespace Lattice

@[simp]
theorem dualLattice_adj (x y : Site 2) :
    dualLattice.Adj x y ↔ (∑ i, (x i - y i).natAbs) = 1 := Iff.rfl


end Lattice
end StatMech
