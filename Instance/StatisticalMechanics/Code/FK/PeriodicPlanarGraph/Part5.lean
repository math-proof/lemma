/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part14
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


noncomputable instance hexagonalGraph_locallyFinite :
    SimpleGraph.LocallyFinite hexagonalGraph := fun u =>
  Fintype.ofFinset (Finset.univ.image (hexagonalNeighbor u)) (by
    intro v
    rw [SimpleGraph.mem_neighborSet]
    exact ⟨(fun hv => by
        rw [Finset.mem_image] at hv
        obtain ⟨i, _, rfl⟩ := hv
        exact hexagonal_adj_neighbor u i),
      hexagonal_mem_candidates_of_adj⟩)


end PeriodicPlanar
end FK
end StatMech
