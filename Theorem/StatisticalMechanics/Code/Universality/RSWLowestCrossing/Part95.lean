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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part93
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem RlcAxisBarrierGap.verticalEdge_mem_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) {t : ℤ}
    (hlower : G.lower ≤ t) (hupper : t < G.upper) :
    s(![0, t], ![0, t + 1]) ∈ rlc_mixedAxisGapEdges G := by
  rw [rlc_mixedAxisGapEdges, Finset.mem_sdiff]
  constructor
  · simp only [Finset.mem_union]
    exact Or.inl (Or.inl (G.verticalEdge_mem_axisGapEdges hn hlower hupper))
  · rw [Finset.mem_union]
    push Not
    constructor
    · intro he
      have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
      by_cases heq : t = G.lower
      · have hfree := G.interior_free (t + 1) (by omega) (by omega)
        exact hfree (by simp [rlc_connectorBarrier, hends.2])
      · have hfree := G.interior_free t (by omega) hupper
        exact hfree (by simp [rlc_connectorBarrier, hends.1])
    · intro he
      have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 he
      by_cases heq : t = G.lower
      · have hfree := G.interior_free (t + 1) (by omega) (by omega)
        exact hfree (by simp [rlc_connectorBarrier, hends.2])
      · have hfree := G.interior_free t (by omega) hupper
        exact hfree (by simp [rlc_connectorBarrier, hends.1])

theorem rlc_rightPathEdges_disjoint_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    Disjoint (rlc_pathEdges gamma.1) (rlc_mixedAxisGapEdges G) := by
  rw [Finset.disjoint_left]
  intro e he hmix
  exact (Finset.mem_sdiff.mp hmix).2 (by simp [he])

theorem rlc_leftPathEdges_disjoint_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    Disjoint (rlc_pathEdges gamma'.1) (rlc_mixedAxisGapEdges G) := by
  rw [Finset.disjoint_left]
  intro e he hmix
  exact (Finset.mem_sdiff.mp hmix).2 (by simp [he])


end Universality
end StatMech
