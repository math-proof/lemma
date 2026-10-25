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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part64
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


@[simp] theorem rlc_rightLeftTraceMinSide_val {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_rightLeftTraceMinSide gamma delta : Site 2) =
      rlc_rightLeftTraceMinVertex gamma delta := by
  rfl


theorem rlc_rightLeftTraceMinVertex_mem_jointBottomTraceFrontier {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightLeftTraceMinVertex gamma delta ∈
      rlc_jointBottomTraceFrontier gamma delta := by
  classical
  let m := rlc_rightLeftTraceMin gamma delta
  let z : Site 2 := rlc_rightLeftTraceMinVertex gamma delta
  have hzUnion := rlc_rightLeftTraceMinVertex_mem_union gamma delta
  have hzPath : z ∈ rlc_pathVertices gamma.1 ∨
      z ∈ rlc_pathVertices delta.1 := by
    simpa [z] using Finset.mem_union.mp hzUnion
  have hzRect : z ∈ rect 0 (2 * n) (-n) n := by
    rcases hzPath with hzGamma | hzDelta
    · exact rlc_pathVertex_mem_rect gamma.1 hzGamma
    · exact rlc_pathVertex_mem_rect delta.1 hzDelta
  have hmLower : -n ≤ m := by
    rw [mem_rect] at hzRect
    simpa [z, m, rlc_rightLeftTraceMinVertex] using hzRect.2.2.1
  by_cases hm : m = -n
  · right
    refine ⟨?_, ?_⟩
    · rw [mem_bottomSide]
      exact ⟨hzRect, by simp [z, m, rlc_rightLeftTraceMinVertex, hm]⟩
    · exact hzPath
  · left
    refine ⟨hzRect, hzPath, ?_⟩
    let x : Site 2 := ![0, -n]
    let u : Site 2 := ![0, m - 1]
    have hxm : -n ≤ m - 1 := by omega
    let w : (hypercubicLattice 2).Walk x u := sw_vertSeg 0 (-n) (m - 1)
    have hn0 : 0 ≤ 2 * n := by
      rw [mem_rect] at hzRect
      exact hzRect.2.1
    have hsupport : ∀ q ∈ w.support,
        q ∈ rect 0 (2 * n) (-n) n ∧
          q ∉ rlc_pathVertices gamma.1 ∧
          q ∉ rlc_pathVertices delta.1 := by
      intro q hq
      rw [sw_vertSeg_mem_support] at hq
      obtain ⟨t, ht, rfl⟩ := hq
      rw [Set.uIcc_of_le hxm] at ht
      rcases ht with ⟨htLower, htUpper⟩
      have hbox : (![0, t] : Site 2) ∈ rect 0 (2 * n) (-n) n := by
        rw [mem_rect]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have hmUpper : m ≤ n := by
          rw [mem_rect] at hzRect
          simpa [z, m, rlc_rightLeftTraceMinVertex] using hzRect.2.2.2
        exact ⟨le_rfl, hn0, htLower, htUpper.trans (by omega)⟩
      have avoid : ∀ eta : RlcRightDiagonalPath n,
          (eta = gamma ∨ eta = delta) →
          (![0, t] : Site 2) ∉ rlc_pathVertices eta.1 := by
        intro eta heta htPath
        have htHeight : t ∈ rlc_rightLeftTraceHeights gamma delta := by
          rw [rlc_rightLeftTraceHeights, Finset.mem_image]
          refine ⟨(![0, t] : Site 2), ?_, by simp⟩
          rw [Finset.mem_filter, Finset.mem_union]
          refine ⟨?_, by simp⟩
          rcases heta with rfl | rfl
          · exact Or.inl htPath
          · exact Or.inr htPath
        have hmt : m ≤ t := Finset.min'_le _ _ htHeight
        exact (by omega)
      exact ⟨hbox, avoid gamma (Or.inl rfl), avoid delta (Or.inr rfl)⟩
    have hxBottom : x ∈ bottomSide 0 (2 * n) (-n) n := by
      rw [mem_bottomSide]
      constructor
      · rw [mem_rect]
        simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one]
        exact ⟨le_rfl, hn0, le_rfl, by omega⟩
      · simp [x]
    have hw : (rlc_rightPairAvoidGraph gamma delta).Walk x u := by
      apply w.transfer (rlc_rightPairAvoidGraph gamma delta)
      intro e he
      induction e using Sym2.inductionOn with
      | _ a b =>
          have hab := w.adj_of_mem_edges he
          have ha := hsupport a (w.fst_mem_support_of_mem_edges he)
          have hb := hsupport b (w.snd_mem_support_of_mem_edges he)
          exact ⟨hab, ha.1, hb.1, ha.2.1, hb.2.1,
            ha.2.2, hb.2.2⟩
    have huJoint : u ∈ rlc_jointBottomSet gamma delta := by
      have hx := hsupport x w.start_mem_support
      exact ⟨x, hxBottom, hx.2.1, hx.2.2, ⟨hw⟩⟩
    have huz : (hypercubicLattice 2).Adj u z := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp only [u, z, rlc_rightLeftTraceMinVertex,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    exact ⟨u, huJoint, huz⟩


end Universality
end StatMech
