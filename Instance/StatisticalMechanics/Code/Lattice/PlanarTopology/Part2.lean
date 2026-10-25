/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

instance instLocallyFinite (d : ℕ) : SimpleGraph.LocallyFinite (hypercubicLattice d) :=
  fun x =>
    Fintype.ofFinset ((candFinset d x).filter (fun y => (hypercubicLattice d).Adj x y)) (by
      intro y
      rw [Finset.mem_filter, SimpleGraph.mem_neighborSet]
      exact ⟨fun h => h.2, fun h => ⟨mem_candFinset_of_adj d x y h, h⟩⟩)


end Lattice
end StatMech
