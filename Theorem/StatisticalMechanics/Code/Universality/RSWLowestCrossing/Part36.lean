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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part35
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_topSide_disjoint_strictBelowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (topSide 0 (2 * n) (-n) n) (rlc_strictBelowSet gamma) := by
  rw [Set.disjoint_left]
  intro z hzTop hzBelow
  obtain ⟨x, hxBottom, hxPath, hreach⟩ := hzBelow
  obtain ⟨w⟩ := hreach
  let ws : (hypercubicLattice 2).Walk (crf_swap x) (crf_swap z) :=
    w.map (rlc_swapRightAvoidHom gamma)
  have hwsBox : ∀ p ∈ ws.support, p ∈ rect (-n) n 0 (2 * n) := by
    intro p hp
    dsimp only [ws] at hp
    have hsupp := SimpleGraph.Walk.support_map
      (rlc_swapRightAvoidHom gamma) w
    have hp' : p ∈ List.map (⇑(rlc_swapRightAvoidHom gamma)) w.support := by
      rw [← hsupp]
      exact hp
    rw [List.mem_map] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    have hqData := rlc_rightPathAvoidGraph_walk_dest gamma
      hxBottom.1 hxPath (w.takeUntil q hq)
    exact (crf_mem_rect_swap 0 (2 * n) (-n) n q).mp hqData.1
  obtain ⟨p, hpws, hpPath⟩ := tpc_two_paths_cross_of_sep
    (rlc_rightPath_arcSeparatingSet hn gamma)
    ((crf_mem_rect_swap 0 (2 * n) (-n) n x).mp hxBottom.1)
    ((crf_mem_rect_swap 0 (2 * n) (-n) n z).mp hzTop.1)
    (by simpa using hxBottom.2) (by simpa using hzTop.2) ws hwsBox
  dsimp only [ws] at hpws
  have hsupp := SimpleGraph.Walk.support_map
    (rlc_swapRightAvoidHom gamma) w
  have hpws' : p ∈ List.map (⇑(rlc_swapRightAvoidHom gamma)) w.support := by
    rw [← hsupp]
    exact hpws
  rw [List.mem_map] at hpws'
  obtain ⟨q, hq, hqp⟩ := hpws'
  rw [rlc_swappedRightPathSupport_eq] at hpPath
  obtain ⟨r, hrPath, hrp⟩ := hpPath
  have hqr : (q : Site 2) = r := by
    apply crf_swap.injective
    exact hqp.trans hrp.symm
  have hqData := rlc_rightPathAvoidGraph_walk_dest gamma
    hxBottom.1 hxPath (w.takeUntil q hq)
  exact hqData.2 (hqr ▸ hrPath)


theorem rlc_strictBelowSet_subset_belowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    rlc_strictBelowSet gamma ⊆ rlc_belowSet hn gamma := by
  rintro z ⟨x, hxBottom, hxPath, hreach⟩
  obtain ⟨w⟩ := hreach
  have hxBelow : x ∈ rlc_belowSet hn gamma :=
    rlc_bottomSide_subset_belowSet hn gamma hxBottom
  have walk_stays : ∀ {a c : Site 2}
      (q : (rlc_rightPathAvoidGraph gamma).Walk a c),
      a ∈ rlc_belowSet hn gamma → c ∈ rlc_belowSet hn gamma := by
    intro a c q haBelow
    induction q with
    | nil => exact haBelow
    | @cons a b c hab q ih =>
      have hbBelow : b ∈ rlc_belowSet hn gamma := by
        by_contra hbBelow
        have hbd : bdEdge (rlc_belowSet hn gamma) s(a, b) := by
          rw [bdEdge_mk]
          exact iff_of_true haBelow hbBelow
        rcases rlc_belowSet_boundary_path hn gamma hab.2.1 hab.2.2.1
            hab.1 hbd with haPath | hbPath
        · exact hab.2.2.2.1 haPath
        · exact hab.2.2.2.2 hbPath
      exact ih hbBelow
  exact walk_stays w hxBelow


theorem rlc_strictTopSet_disjoint_belowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (rlc_strictTopSet gamma) (rlc_belowSet hn gamma) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxTop, hxPath, hreach⟩ hzBelow
  obtain ⟨w⟩ := hreach
  have hxOutside : x ∉ rlc_belowSet hn gamma :=
    (Set.disjoint_left.mp (rlc_topSide_disjoint_belowSet hn gamma)) hxTop
  have walk_stays : ∀ {a c : Site 2}
      (q : (rlc_rightPathAvoidGraph gamma).Walk a c),
      a ∉ rlc_belowSet hn gamma → c ∉ rlc_belowSet hn gamma := by
    intro a c q haOutside
    induction q with
    | nil => exact haOutside
    | @cons a b c hab q ih =>
      have hbOutside : b ∉ rlc_belowSet hn gamma := by
        intro hbBelow
        have hbd : bdEdge (rlc_belowSet hn gamma) s(a, b) := by
          rw [bdEdge_mk]
          exact iff_of_false haOutside (not_not.mpr hbBelow)
        rcases rlc_belowSet_boundary_path hn gamma hab.2.1 hab.2.2.1
            hab.1 hbd with haPath | hbPath
        · exact hab.2.2.2.1 haPath
        · exact hab.2.2.2.2 hbPath
      exact ih hbOutside
  exact (walk_stays w hxOutside) hzBelow

theorem rlc_strictTopSet_disjoint_strictBelowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (rlc_strictTopSet gamma) (rlc_strictBelowSet gamma) :=
  (rlc_strictTopSet_disjoint_belowSet hn gamma).mono_right
    (rlc_strictBelowSet_subset_belowSet hn gamma)


theorem rlc_disjointRightPaths_not_mutually_top {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    ¬ ((rlc_pathVertices gamma.1 : Set (Site 2)) ⊆
          rlc_strictTopSet delta ∧
        (rlc_pathVertices delta.1 : Set (Site 2)) ⊆
          rlc_strictTopSet gamma) := by
  rintro ⟨hgammaTop, hdeltaTop⟩
  let x : Site 2 := ![0, -n]
  have hxBottom : x ∈ bottomSide 0 (2 * n) (-n) n := by
    rw [mem_bottomSide, mem_rect]
    simp [x]
    omega
  by_cases hxDelta : x ∈ rlc_pathVertices delta.1
  · have hxNotGamma : x ∉ rlc_pathVertices gamma.1 := fun hxGamma =>
      (Finset.disjoint_left.mp hdisj) hxGamma hxDelta
    have hxBelowGamma : x ∈ rlc_strictBelowSet gamma :=
      ⟨x, hxBottom, hxNotGamma, SimpleGraph.Reachable.refl x⟩
    exact (Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_strictBelowSet hn gamma))
        (hdeltaTop hxDelta) hxBelowGamma
  · have hxBelowDelta : x ∈ rlc_strictBelowSet delta :=
      ⟨x, hxBottom, hxDelta, SimpleGraph.Reachable.refl x⟩
    have hbelowDisjGamma : Disjoint (rlc_strictBelowSet delta)
        (rlc_pathVertices gamma.1 : Set (Site 2)) := by
      rw [Set.disjoint_left]
      intro z hzBelow hzGamma
      exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn delta))
          (hgammaTop hzGamma) hzBelow
    have hbelowMono : rlc_strictBelowSet delta ⊆
        rlc_strictBelowSet gamma :=
      rlc_strictBelowSet_mono_of_disjoint_path
        delta gamma hbelowDisjGamma
    let y : Site 2 := ![0, n]
    have hyTop : y ∈ topSide 0 (2 * n) (-n) n := by
      rw [mem_topSide, mem_rect]
      simp [y]
      omega
    have hyNotBelow : y ∉ rlc_strictBelowSet delta := fun hy =>
      (Set.disjoint_left.mp
        (rlc_topSide_disjoint_strictBelowSet hn delta)) hyTop hy
    let w : (hypercubicLattice 2).Walk x y := sw_vertSeg 0 (-n) n
    have hwRect : ∀ z ∈ w.support, z ∈ rect 0 (2 * n) (-n) n := by
      intro z hz
      have hz' := sw_vertSeg_support_subset 0 (-n) n hz
      obtain ⟨t, ht, rfl⟩ := hz'
      rw [Set.uIcc_of_le (by omega)] at ht
      change -n ≤ t ∧ t ≤ n at ht
      rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    obtain ⟨a, b, hab, haBelow, hbNotBelow, haRect, hbRect⟩ :=
      crr_walk_exit_set_in_box (rlc_strictBelowSet delta)
        (rect 0 (2 * n) (-n) n) w hwRect hxBelowDelta hyNotBelow
    have hbd : bdEdge (rlc_strictBelowSet delta) s(a, b) := by
      rw [bdEdge_mk]
      exact iff_of_true haBelow hbNotBelow
    have hbDelta : b ∈ rlc_pathVertices delta.1 := by
      rcases rlc_strictBelowSet_boundary_path delta haRect hbRect hab hbd with
        haDelta | hbDelta
      · exact False.elim ((Set.disjoint_left.mp
          (rlc_strictBelowSet_disjoint_path delta)) haBelow haDelta)
      · exact hbDelta
    have hbNotGamma : b ∉ rlc_pathVertices gamma.1 := fun hbGamma =>
      (Finset.disjoint_left.mp hdisj) hbGamma hbDelta
    have haBelowGamma : a ∈ rlc_strictBelowSet gamma := hbelowMono haBelow
    have hbBelowGamma : b ∈ rlc_strictBelowSet gamma :=
      rlc_strictBelowSet_step gamma haBelowGamma hbRect hbNotGamma hab
    exact (Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_strictBelowSet hn gamma))
        (hdeltaTop hbDelta) hbBelowGamma


end Universality
end StatMech
