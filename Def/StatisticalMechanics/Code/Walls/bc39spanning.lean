/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable def bc39_transferWalk (S : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {a b : Site d} (p : (openSubgraph d ω).Walk a b) (hp : ∀ v ∈ p.support, v ∉ S) :
    (openSubgraph d (removeSites S ω)).Walk a b := by
  refine p.transfer _ ?_
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet]
    have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
    have hadj : (openSubgraph d ω).Adj u v := by
      rw [← SimpleGraph.mem_edgeSet]; exact p.edges_subset_edgeSet he
    exact bc39_openEdge_removeSites_of_notMem S ω (hp _ hu) (hp _ hv) hadj


end StatMech.Walls
