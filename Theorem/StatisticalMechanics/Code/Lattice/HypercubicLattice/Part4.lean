/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part4
open Set Finset


namespace StatMech

namespace Lattice

@[simp]
theorem mem_vertexBoundary {d n : ℕ} {x : Site d} :
    x ∈ vertexBoundary d n ↔ x ∈ box d n ∧ x ∉ box d (n - 1) := Iff.rfl

theorem vertexBoundary_finite (d n : ℕ) : (vertexBoundary d n).Finite :=
  (box_finite d n).subset (Set.diff_subset)


end Lattice
end StatMech
