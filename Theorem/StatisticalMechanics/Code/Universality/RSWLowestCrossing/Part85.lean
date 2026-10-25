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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part83
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem RlcAxisBarrierGap.verticalEdge_mem_axisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n) {t : ℤ}
    (hlower : G.lower ≤ t) (hupper : t < G.upper) :
    s(![0, t], ![0, t + 1]) ∈ rlc_axisGapEdges G := by
  by_cases heq : t = G.lower
  · subst t
    simp [rlc_axisGapEdges, RlcAxisBarrierGap.firstEdge,
      RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.seedVertex]
  · have hlt : G.lower < t := lt_of_le_of_ne hlower (Ne.symm heq)
    have htRegion := G.axisVertex_mem_region_of_between hn hlt hupper
    rw [rlc_axisGapEdges, Finset.mem_union]
    apply Or.inl
    simp only [Finset.mem_filter]
    constructor
    · rw [mem_edgesWithinFinset]
      have htSet : ![0, t] ∈ rlc_axisGapRegionSet G := by
        simpa [rlc_axisGapRegion] using htRegion
      obtain ⟨htAllowed, _hs, _hreach⟩ := htSet
      have htBox := (Finset.mem_sdiff.mp htAllowed).1
      have hnextBox : ![0, t + 1] ∈ rlc_connectorBox n := by
        have hlowerBox := rlc_rightPathVertex_mem_connectorBox
          gamma G.lowerVertex_mem_right
        have hupperBox := rlc_leftPathVertex_mem_connectorBox
          gamma' G.upperVertex_mem_left
        simp only [RlcAxisBarrierGap.lowerVertex,
          RlcAxisBarrierGap.upperVertex, mem_rect, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hlowerBox hupperBox
        simp only [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
      exact ⟨![0, t], htBox, ![0, t + 1], hnextBox, rfl⟩
    · exact ⟨![0, t], htRegion, Sym2.mem_mk_left _ _⟩


end Universality
end StatMech
