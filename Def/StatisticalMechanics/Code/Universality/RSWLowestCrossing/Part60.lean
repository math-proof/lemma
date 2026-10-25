/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part60
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


def rlc_rightTraceGraph {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    SimpleGraph (rect 0 (2 * n) (-n) n) where
  Adj u v :=
    ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Adj u v ∧
      s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩


noncomputable def rlc_rightTraceGraph_walk_left {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_rightTraceGraph gamma delta).Walk
      ⟨gamma.1.1, leftSide_subset gamma.1.1.2⟩
      ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ := by
  apply gamma.1.2.2.1.transfer (rlc_rightTraceGraph gamma delta)
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have heAmb : s((u : Site 2), (v : Site 2)) ∈
          rlc_pathEdges gamma.1 := by
        simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
        exact ⟨s(u, v), he, by simp⟩
      exact ⟨gamma.1.2.2.1.adj_of_mem_edges he,
        Finset.mem_union_left _ heAmb⟩


noncomputable def rlc_rightTraceGraph_walk_right {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_rightTraceGraph gamma delta).Walk
      ⟨delta.1.1, leftSide_subset delta.1.1.2⟩
      ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
  apply delta.1.2.2.1.transfer (rlc_rightTraceGraph gamma delta)
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have heAmb : s((u : Site 2), (v : Site 2)) ∈
          rlc_pathEdges delta.1 := by
        simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
        exact ⟨s(u, v), he, by simp⟩
      exact ⟨delta.1.2.2.1.adj_of_mem_edges he,
        Finset.mem_union_right _ heAmb⟩


end Universality
end StatMech
