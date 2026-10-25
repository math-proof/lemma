/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part2
open Set


namespace StatMech

namespace Lattice

variable {d : ℕ}


@[simp]
theorem openSubgraph_adj (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    (openSubgraph d ω).Adj x y ↔ (hypercubicLattice d).Adj x y ∧ ω s(x, y) = true :=
  Iff.rfl


theorem openSubgraph_le (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d ω ≤ hypercubicLattice d := fun _ _ h => h.1


end Lattice
end StatMech
