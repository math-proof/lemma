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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part82
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem RlcAxisBarrierGap.seedVertex_mem_region_of_lt {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (h : G.lower + 1 < G.upper) :
    G.seedVertex ∈ rlc_axisGapRegion G := by
  have hs := G.seedVertex_mem_allowed_of_lt hn h
  have hsSet : G.seedVertex ∈ rlc_axisGapRegionSet G :=
    ⟨hs, hs, SimpleGraph.Reachable.refl _⟩
  simpa [rlc_axisGapRegion] using hsSet


theorem RlcAxisBarrierGap.axisVertex_mem_region_of_between {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n) {t : ℤ}
    (hlower : G.lower < t) (hupper : t < G.upper) :
    ![0, t] ∈ rlc_axisGapRegion G := by
  have hgap : G.lower + 1 < G.upper := by omega
  have hs := G.seedVertex_mem_allowed_of_lt hn hgap
  have hzBox : ![0, t] ∈ rlc_connectorBox n := by
    have hlowerBox := rlc_rightPathVertex_mem_connectorBox
      gamma G.lowerVertex_mem_right
    have hupperBox := rlc_leftPathVertex_mem_connectorBox
      gamma' G.upperVertex_mem_left
    simp only [RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.upperVertex,
      mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one] at hlowerBox hupperBox
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hzAllowed : ![0, t] ∈ rlc_connectorAllowed gamma gamma' := by
    rw [rlc_connectorAllowed, Finset.mem_sdiff]
    exact ⟨hzBox, G.interior_free t hlower hupper⟩
  let w := sw_vertSeg 0 (G.lower + 1) t
  have hw : ∀ z ∈ w.support,
      z ∈ (rlc_connectorAllowed gamma gamma' : Set (Site 2)) := by
    intro z hz
    change z ∈ (sw_vertSeg 0 (G.lower + 1) t).support at hz
    rw [sw_vertSeg_mem_support, Set.uIcc_of_le (by omega)] at hz
    simp only [Set.mem_Icc] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    rw [Finset.mem_coe, rlc_connectorAllowed, Finset.mem_sdiff]
    constructor
    · have hlowerBox := rlc_rightPathVertex_mem_connectorBox
        gamma G.lowerVertex_mem_right
      have hupperBox := rlc_leftPathVertex_mem_connectorBox
        gamma' G.upperVertex_mem_left
      simp only [RlcAxisBarrierGap.lowerVertex,
        RlcAxisBarrierGap.upperVertex, mem_rect, Matrix.cons_val_zero,
        Matrix.cons_val_one] at hlowerBox hupperBox
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · exact G.interior_free r (by omega) (by omega)
  have hreach := walk_induce_reachable (hypercubicLattice 2)
    (rlc_connectorAllowed gamma gamma' : Set (Site 2))
    w hw hs hzAllowed
  have hzSet : ![0, t] ∈ rlc_axisGapRegionSet G :=
    ⟨hzAllowed, hs, hreach⟩
  simpa [rlc_axisGapRegion] using hzSet


end Universality
end StatMech
