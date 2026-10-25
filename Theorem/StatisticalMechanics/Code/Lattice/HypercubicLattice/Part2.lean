/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part2
open Set Finset


namespace StatMech

namespace Lattice

@[simp]
theorem hypercubicLattice_adj (d : ℕ) (x y : Site d) :
    (hypercubicLattice d).Adj x y ↔ (∑ i, (x i - y i).natAbs) = 1 := Iff.rfl


end Lattice
end StatMech
