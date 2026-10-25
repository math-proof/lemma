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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part41
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_leftBottomSide_disjoint_strictAboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (bottomSide (-2 * n) 0 (-n) n)
      (rlc_strictAboveSet gamma) := by
  rw [Set.disjoint_left]
  intro z hzBottom hzAbove
  obtain ⟨x, hxTop, hxPath, hreach⟩ := hzAbove
  obtain ⟨w⟩ := hreach
  let ws : (hypercubicLattice 2).Walk (crf_swap z) (crf_swap x) :=
    w.reverse.map (rlc_swapLeftAvoidHom gamma)
  have hwsBox : ∀ p ∈ ws.support, p ∈ rect (-n) n (-2 * n) 0 := by
    intro p hp
    dsimp only [ws] at hp
    have hsupp := SimpleGraph.Walk.support_map
      (rlc_swapLeftAvoidHom gamma) w.reverse
    have hp' : p ∈ List.map (⇑(rlc_swapLeftAvoidHom gamma))
        w.reverse.support := by
      rw [← hsupp]
      exact hp
    rw [List.mem_map] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    have hq' : q ∈ w.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hq
    have hqData := rlc_leftPathAvoidGraph_walk_dest gamma
      hxTop.1 hxPath (w.takeUntil q hq')
    exact (crf_mem_rect_swap (-2 * n) 0 (-n) n q).mp hqData.1
  obtain ⟨p, hpws, hpPath⟩ := tpc_two_paths_cross_of_sep
    (rlc_leftPath_arcSeparatingSet hn gamma)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n z).mp hzBottom.1)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n x).mp hxTop.1)
    (by simpa using hzBottom.2) (by simpa using hxTop.2) ws hwsBox
  dsimp only [ws] at hpws
  have hsupp := SimpleGraph.Walk.support_map
    (rlc_swapLeftAvoidHom gamma) w.reverse
  have hpws' : p ∈ List.map (⇑(rlc_swapLeftAvoidHom gamma))
      w.reverse.support := by
    rw [← hsupp]
    exact hpws
  rw [List.mem_map] at hpws'
  obtain ⟨q, hq, hqp⟩ := hpws'
  have hq' : q ∈ w.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hq
  rw [rlc_swappedLeftPathSupport_eq] at hpPath
  obtain ⟨r, hrPath, hrp⟩ := hpPath
  have hqr : (q : Site 2) = r := by
    apply crf_swap.injective
    exact hqp.trans hrp.symm
  have hqData := rlc_leftPathAvoidGraph_walk_dest gamma
    hxTop.1 hxPath (w.takeUntil q hq')
  exact hqData.2 (hqr ▸ hrPath)


theorem rlc_strictAboveSet_subset_aboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    rlc_strictAboveSet gamma ⊆ rlc_aboveSet hn gamma := by
  rintro z ⟨x, hxTop, hxPath, hreach⟩
  obtain ⟨w⟩ := hreach
  have hxAbove : x ∈ rlc_aboveSet hn gamma :=
    rlc_leftTopSide_subset_aboveSet hn gamma hxTop
  have walk_stays : ∀ {a c : Site 2}
      (q : (rlc_leftPathAvoidGraph gamma).Walk a c),
      a ∈ rlc_aboveSet hn gamma → c ∈ rlc_aboveSet hn gamma := by
    intro a c q haAbove
    induction q with
    | nil => exact haAbove
    | @cons a b c hab q ih =>
      have hbAbove : b ∈ rlc_aboveSet hn gamma := by
        by_contra hbAbove
        have hbd : bdEdge (rlc_aboveSet hn gamma) s(a, b) := by
          rw [bdEdge_mk]
          exact iff_of_true haAbove hbAbove
        rcases rlc_aboveSet_boundary_path hn gamma hab.2.1 hab.2.2.1
            hab.1 hbd with haPath | hbPath
        · exact hab.2.2.2.1 haPath
        · exact hab.2.2.2.2 hbPath
      exact ih hbAbove
  exact walk_stays w hxAbove


theorem rlc_strictBottomSet_disjoint_aboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (rlc_strictBottomSet gamma) (rlc_aboveSet hn gamma) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxBottom, hxPath, hreach⟩ hzAbove
  obtain ⟨w⟩ := hreach
  have hxOutside : x ∉ rlc_aboveSet hn gamma :=
    (Set.disjoint_left.mp
      (rlc_leftBottomSide_disjoint_aboveSet hn gamma)) hxBottom
  have walk_stays : ∀ {a c : Site 2}
      (q : (rlc_leftPathAvoidGraph gamma).Walk a c),
      a ∉ rlc_aboveSet hn gamma → c ∉ rlc_aboveSet hn gamma := by
    intro a c q haOutside
    induction q with
    | nil => exact haOutside
    | @cons a b c hab q ih =>
      have hbOutside : b ∉ rlc_aboveSet hn gamma := by
        intro hbAbove
        have hbd : bdEdge (rlc_aboveSet hn gamma) s(a, b) := by
          rw [bdEdge_mk]
          exact iff_of_false haOutside (not_not.mpr hbAbove)
        rcases rlc_aboveSet_boundary_path hn gamma hab.2.1 hab.2.2.1
            hab.1 hbd with haPath | hbPath
        · exact hab.2.2.2.1 haPath
        · exact hab.2.2.2.2 hbPath
      exact ih hbOutside
  exact (walk_stays w hxOutside) hzAbove

theorem rlc_strictBottomSet_disjoint_strictAboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (rlc_strictBottomSet gamma) (rlc_strictAboveSet gamma) :=
  (rlc_strictBottomSet_disjoint_aboveSet hn gamma).mono_right
    (rlc_strictAboveSet_subset_aboveSet hn gamma)

theorem rlc_strictBelowSet_finite {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    (rlc_strictBelowSet gamma).Finite :=
  (rect_finite 0 (2 * n) (-n) n).subset
    (rlc_strictBelowSet_subset_box gamma)

theorem rlc_strictAboveSet_finite {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    (rlc_strictAboveSet gamma).Finite :=
  (rect_finite (-2 * n) 0 (-n) n).subset
    (rlc_strictAboveSet_subset_box gamma)

theorem rlc_strictTopSet_finite {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    (rlc_strictTopSet gamma).Finite :=
  (rect_finite 0 (2 * n) (-n) n).subset
    (rlc_strictTopSet_subset_box gamma)

theorem rlc_strictBottomSet_finite {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    (rlc_strictBottomSet gamma).Finite :=
  (rect_finite (-2 * n) 0 (-n) n).subset
    (rlc_strictBottomSet_subset_box gamma)

theorem rlc_bdEdge_inter {S T : Set (Site 2)} {e : Sym2 (Site 2)}
    (h : bdEdge (S ∩ T) e) : bdEdge S e ∨ bdEdge T e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [bdEdge_mk, Set.mem_inter_iff] at h ⊢
      tauto

theorem rlc_bdEdge_union {S T : Set (Site 2)} {e : Sym2 (Site 2)}
    (h : bdEdge (S ∪ T) e) : bdEdge S e ∨ bdEdge T e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [bdEdge_mk, Set.mem_union] at h ⊢
      tauto

end Universality
end StatMech
