/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc35globalarm
import Theorem.StatisticalMechanics.Code.Walls.bc36rooteddiv.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc38_exists_closer_neighbour {V : Type*} (G : SimpleGraph V) {root v : V}
    (hr : G.Reachable root v) (hne : v ≠ root) :
    ∃ u, G.Adj v u ∧ G.dist root u < G.dist root v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hdvpos : 0 < G.dist root v := by
    apply Nat.pos_of_ne_zero
    rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]
    exact ⟨hne.symm, hr⟩
  have hpnn : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hp]; omega
  refine ⟨p.penultimate, (p.adj_penultimate hpnn).symm, ?_⟩
  have hdl : G.dist root p.penultimate ≤ p.dropLast.length := SimpleGraph.dist_le p.dropLast
  rw [SimpleGraph.Walk.length_dropLast, hp] at hdl
  omega

end StatMech.Walls
