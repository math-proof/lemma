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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part63
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rightLeftTraceMin_mem_heights {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightLeftTraceMin gamma delta ∈
      rlc_rightLeftTraceHeights gamma delta := by
  exact Finset.min'_mem _ _

theorem rlc_rightLeftTraceMinVertex_mem_union {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightLeftTraceMinVertex gamma delta ∈
      rlc_pathVertices gamma.1 ∪ rlc_pathVertices delta.1 := by
  classical
  have hmin := rlc_rightLeftTraceMin_mem_heights gamma delta
  rw [rlc_rightLeftTraceHeights, Finset.mem_image] at hmin
  obtain ⟨z, hz, hzmin⟩ := hmin
  rw [Finset.mem_filter] at hz
  have hzeq : z = rlc_rightLeftTraceMinVertex gamma delta := by
    apply funext
    intro i
    fin_cases i
    · simpa [rlc_rightLeftTraceMinVertex] using hz.2
    · simpa [rlc_rightLeftTraceMinVertex] using hzmin
  rw [← hzeq]
  exact hz.1

theorem rlc_rightLeftTraceMinVertex_lowerHalf {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightLeftTraceMinVertex gamma delta ∈ rlc_lowerHalf := by
  have hstart : (gamma.1.1 : Site 2) 1 ∈
      rlc_rightLeftTraceHeights gamma delta := by
    classical
    rw [rlc_rightLeftTraceHeights, Finset.mem_image]
    refine ⟨(gamma.1.1 : Site 2), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_union]
    exact ⟨Or.inl (rlc_path_start_mem_vertices gamma.1), gamma.1.1.2.2⟩
  have hle : rlc_rightLeftTraceMin gamma delta ≤
      (gamma.1.1 : Site 2) 1 :=
    Finset.min'_le _ _ hstart
  exact hle.trans gamma.2.1


theorem rlc_rightLeftTraceMinVertex_mem_strictBelow_of_not_path {n : ℤ}
    (gamma delta eta : RlcRightDiagonalPath n)
    (heta : eta = gamma ∨ eta = delta)
    (hnot : rlc_rightLeftTraceMinVertex gamma delta ∉
      rlc_pathVertices eta.1) :
    rlc_rightLeftTraceMinVertex gamma delta ∈
      rlc_strictBelowSet eta := by
  classical
  let m := rlc_rightLeftTraceMin gamma delta
  let z : Site 2 := rlc_rightLeftTraceMinVertex gamma delta
  have hzUnion := rlc_rightLeftTraceMinVertex_mem_union gamma delta
  have hzRect : z ∈ rect 0 (2 * n) (-n) n := by
    rcases Finset.mem_union.mp hzUnion with hz | hz
    · exact rlc_pathVertex_mem_rect gamma.1 hz
    · exact rlc_pathVertex_mem_rect delta.1 hz
  have hmLower : -n ≤ m := by
    rw [mem_rect] at hzRect
    simpa [z, m, rlc_rightLeftTraceMinVertex] using hzRect.2.2.1
  have hmUpper : m ≤ n := by
    rw [mem_rect] at hzRect
    simpa [z, m, rlc_rightLeftTraceMinVertex] using hzRect.2.2.2
  let w := sw_vertSeg 0 (-n) m
  have hsupport : ∀ q ∈ w.support,
      q ∈ rect 0 (2 * n) (-n) n ∧ q ∉ rlc_pathVertices eta.1 := by
    intro q hq
    rw [sw_vertSeg_mem_support] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    rw [Set.uIcc_of_le hmLower] at ht
    rcases ht with ⟨htLower, htUpper⟩
    have hbox : (![0, t] : Site 2) ∈ rect 0 (2 * n) (-n) n := by
      rw [mem_rect]
      have hn0 : 0 ≤ 2 * n := by
        rw [mem_rect] at hzRect
        exact hzRect.2.1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    refine ⟨hbox, ?_⟩
    intro htPath
    have htHeight : t ∈ rlc_rightLeftTraceHeights gamma delta := by
      rw [rlc_rightLeftTraceHeights, Finset.mem_image]
      refine ⟨(![0, t] : Site 2), ?_, by simp⟩
      rw [Finset.mem_filter, Finset.mem_union]
      refine ⟨?_, by simp⟩
      rcases heta with rfl | rfl
      · exact Or.inl htPath
      · exact Or.inr htPath
    have hmt : m ≤ t := Finset.min'_le _ _ htHeight
    have htm : t = m := le_antisymm htUpper hmt
    apply hnot
    simpa [z, m, rlc_rightLeftTraceMinVertex, htm] using htPath
  have hw : (rlc_rightPathAvoidGraph eta).Walk ![0, -n] z := by
    apply w.transfer (rlc_rightPathAvoidGraph eta)
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hab := w.adj_of_mem_edges he
        have ha := hsupport a (w.fst_mem_support_of_mem_edges he)
        have hb := hsupport b (w.snd_mem_support_of_mem_edges he)
        exact ⟨hab, ha.1, hb.1, ha.2, hb.2⟩
  have hbottom : (![0, -n] : Site 2) ∈ bottomSide 0 (2 * n) (-n) n := by
    rw [mem_bottomSide]
    have hn0 : 0 ≤ 2 * n := by
      rw [mem_rect] at hzRect
      exact hzRect.2.1
    constructor
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨le_rfl, hn0, le_rfl, hmLower.trans hmUpper⟩
    · simp
  have hstartAvoid := (hsupport ![0, -n] w.start_mem_support).2
  exact ⟨![0, -n], hbottom, hstartAvoid, ⟨hw⟩⟩


theorem rlc_rightLeftTraceMinVertex_not_upperUnion {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightLeftTraceMinVertex gamma delta ∉
      rlc_rightUpperUnionSet gamma delta := by
  intro htop
  rcases htop with htop | htop
  · by_cases hpath : rlc_rightLeftTraceMinVertex gamma delta ∈
        rlc_pathVertices gamma.1
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) htop hpath
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn gamma)) htop
          (rlc_rightLeftTraceMinVertex_mem_strictBelow_of_not_path
            gamma delta gamma (Or.inl rfl) hpath)
  · by_cases hpath : rlc_rightLeftTraceMinVertex gamma delta ∈
        rlc_pathVertices delta.1
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path delta)) htop hpath
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn delta)) htop
          (rlc_rightLeftTraceMinVertex_mem_strictBelow_of_not_path
            gamma delta delta (Or.inr rfl) hpath)


theorem rlc_exists_safe_left_trace_anchor {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) :
    ∃ x : leftSide 0 (2 * n) (-n) n,
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (x : Site 2) ∈ rlc_pathVertices gamma.1 ∪
        rlc_pathVertices delta.1 ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
  let z := rlc_rightLeftTraceMinVertex gamma delta
  have hzUnion := rlc_rightLeftTraceMinVertex_mem_union gamma delta
  have hzRect : z ∈ rect 0 (2 * n) (-n) n := by
    rcases Finset.mem_union.mp hzUnion with hz | hz
    · exact rlc_pathVertex_mem_rect gamma.1 hz
    · exact rlc_pathVertex_mem_rect delta.1 hz
  have hzLeft : z ∈ leftSide 0 (2 * n) (-n) n := by
    exact ⟨hzRect, by simp [z, rlc_rightLeftTraceMinVertex]⟩
  exact ⟨⟨z, hzLeft⟩,
    rlc_rightLeftTraceMinVertex_lowerHalf gamma delta,
    hzUnion, rlc_rightLeftTraceMinVertex_not_upperUnion hn gamma delta⟩


end Universality
end StatMech
