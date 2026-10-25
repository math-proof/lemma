/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc33escaping.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc34ray.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable instance ray34_locallyFinite_openSubgraph (ω : ConfigSpace (Sym2 (Site d))) :
    SimpleGraph.LocallyFinite (openSubgraph d ω) := by
  classical
  intro x
  apply Fintype.ofFinset
    (((hypercubicLattice d).neighborFinset x).filter (fun y => (openSubgraph d ω).Adj x y))
  intro y
  rw [Finset.mem_filter, SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩


end StatMech.Walls
