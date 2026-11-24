module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bc33escaping.Part2
public import Theorem.StatisticalMechanics.Code.Walls.bc34ray.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
