/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part2
open Set Finset


namespace StatMech

namespace Lattice

def box (d n : ℕ) : Set (Site d) := {x | ∀ i, (x i).natAbs ≤ n}

end Lattice
end StatMech
