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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part80
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem RlcAxisBarrierGap.lowerVertex_mem_right {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.lowerVertex ∈ rlc_pathVertices gamma.1 := by
  simpa [RlcAxisBarrierGap.lowerVertex] using
    (rlc_mem_axisHeights_iff (rlc_pathVertices gamma.1) G.lower).mp G.lower_mem

theorem RlcAxisBarrierGap.upperVertex_mem_left {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.upperVertex ∈ rlc_pathVertices gamma'.1 := by
  simpa [RlcAxisBarrierGap.upperVertex] using
    (rlc_mem_axisHeights_iff (rlc_pathVertices gamma'.1) G.upper).mp G.upper_mem

theorem RlcAxisBarrierGap.seedVertex_not_barrier_of_lt {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (h : G.lower + 1 < G.upper) :
    G.seedVertex ∉ rlc_connectorBarrier gamma gamma' := by
  exact G.interior_free (G.lower + 1) (by omega) h

theorem RlcAxisBarrierGap.seedVertex_mem_box_of_lt {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (h : G.lower + 1 < G.upper) :
    G.seedVertex ∈ rlc_connectorBox n := by
  have hstart := leftSide_subset gamma.1.1.2
  have hfinish := rightSide_subset gamma'.1.2.1.2
  rw [mem_rect] at hstart hfinish
  have hlower : -n ≤ G.lower := le_trans hstart.2.2.1 G.start_le
  have hupper : G.upper ≤ n := le_trans G.upper_le_finish hfinish.2.2.2
  simp only [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect,
    RlcAxisBarrierGap.seedVertex, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

theorem RlcAxisBarrierGap.seedVertex_mem_allowed_of_lt {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (h : G.lower + 1 < G.upper) :
    G.seedVertex ∈ rlc_connectorAllowed gamma gamma' := by
  rw [rlc_connectorAllowed, Finset.mem_sdiff]
  exact ⟨G.seedVertex_mem_box_of_lt hn h, G.seedVertex_not_barrier_of_lt h⟩

theorem RlcAxisBarrierGap.firstEdge_lattice {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.firstEdge ∈ (hypercubicLattice 2).edgeSet := by
  change s(G.lowerVertex, G.seedVertex) ∈ (hypercubicLattice 2).edgeSet
  rw [SimpleGraph.mem_edgeSet]
  simp [RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.seedVertex,
    hypercubicLattice_adj, Fin.sum_univ_two]


end Universality
end StatMech
