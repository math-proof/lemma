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
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part5
open Set


namespace StatMech

namespace Lattice

variable {d : ℕ}


@[simp]
theorem openSubgraphInduce_adj (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d))
    (x y : S) :
    (openSubgraphInduce d ω S).Adj x y ↔ (openSubgraph d ω).Adj x y := Iff.rfl


end Lattice
end StatMech
