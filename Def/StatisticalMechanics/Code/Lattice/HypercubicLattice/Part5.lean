/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part4
open Set Finset


namespace StatMech

namespace Lattice

def edgeBoundary (d : ℕ) (S : Set (Site d)) : Set (Site d × Site d) :=
  {p | (hypercubicLattice d).Adj p.1 p.2 ∧ (p.1 ∈ S ↔ p.2 ∉ S)}

end Lattice
end StatMech
