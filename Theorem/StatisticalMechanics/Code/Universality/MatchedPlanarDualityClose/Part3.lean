/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWFrameReconcileClose.Part3
import Def.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part2
open Set SimpleGraph Finset
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem mpd_leftReach_subset_box (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    mpd_leftReach ω n ⊆ rect 0 (n + 1) 0 n := fun _ hv => hv.1


theorem mpd_leftReach_finite (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (mpd_leftReach ω n).Finite :=
  (rect_finite 0 (n + 1) 0 n).subset (mpd_leftReach_subset_box ω n)


theorem mpd_horizontal_iff_right_in_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    HorizontalCrossing ω 0 (n + 1) 0 n ↔
      ∃ y : Site 2, y ∈ rightSide 0 (n + 1) 0 n ∧ y ∈ mpd_leftReach ω n := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨y, y.2, rightSide_subset y.2, x, x.2, rightSide_subset y.2, hxy⟩
  · rintro ⟨y, hyR, _hybox, x, hxL, hyb, hconn⟩
    exact ⟨⟨x, hxL⟩, ⟨y, hyR⟩, hconn⟩


theorem mpd_leftSide_subset_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {x : Site 2} (hx : x ∈ leftSide 0 (n + 1) 0 n) : x ∈ mpd_leftReach ω n :=
  ⟨leftSide_subset hx, x, hx, leftSide_subset hx,
    connectedWithin_refl ω (rect 0 (n + 1) 0 n) ⟨x, leftSide_subset hx⟩⟩


theorem mpd_rightSide_notin_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) {y : Site 2}
    (hy : y ∈ rightSide 0 (n + 1) 0 n) : y ∉ mpd_leftReach ω n := fun hyL =>
  hnoH ((mpd_horizontal_iff_right_in_leftReach ω n).mpr ⟨y, hy, hyL⟩)


theorem mpd_leftReach_separates (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 (n + 1) 0 n) (hy : y ∈ rightSide 0 (n + 1) 0 n) :
    ¬ (latticeMinusBarrier (mpd_leftReach ω n)).Reachable x y :=
  not_reachable_latticeMinusBarrier (mpd_leftReach ω n)
    (mpd_leftSide_subset_leftReach ω n hx) (mpd_rightSide_notin_leftReach ω n hnoH hy)


theorem mpd_escape_crossCount_odd (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 (n + 1) 0 n) (hy : y ∈ rightSide 0 (n + 1) 0 n)
    (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount (mpd_leftReach ω n) w) :=
  crossCount_odd_of_separated (mpd_leftReach ω n)
    (mpd_leftSide_subset_leftReach ω n hx) (mpd_rightSide_notin_leftReach ω n hnoH hy) w


theorem mpd_leftReach_extend (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (hv : v ∈ mpd_leftReach ω n) (hwbox : w ∈ rect 0 (n + 1) 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hopen : ω s(v, w) = true) :
    w ∈ mpd_leftReach ω n := by
  obtain ⟨_hvbox, x, hxL, hvbox', hconn⟩ := hv
  refine ⟨hwbox, x, hxL, hwbox, ?_⟩
  have hstep : (openSubgraphInduce 2 ω (rect 0 (n + 1) 0 n)).Adj ⟨v, hvbox'⟩ ⟨w, hwbox⟩ := by
    rw [openSubgraphInduce_adj]; exact ⟨hadj, hopen⟩
  exact hconn.trans hstep.reachable


theorem mpd_leftReach_boundary_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (hadj : (hypercubicLattice 2).Adj p q)
    (hbd : bdEdge (mpd_leftReach ω n) s(p, q))
    (hpbox : p ∈ rect 0 (n + 1) 0 n) (hqbox : q ∈ rect 0 (n + 1) 0 n) :
    ω s(p, q) = false := by
  rw [bdEdge_mk] at hbd
  by_cases hp : p ∈ mpd_leftReach ω n
  · by_contra h
    rw [Bool.not_eq_false] at h
    exact (hbd.mp hp) (mpd_leftReach_extend ω n hp hqbox hadj h)
  · have hq : q ∈ mpd_leftReach ω n := by by_contra hqn; exact hp (hbd.mpr hqn)
    rw [Sym2.eq_swap]
    by_contra h
    rw [Bool.not_eq_false] at h
    exact hp (mpd_leftReach_extend ω n hq hpbox hadj.symm h)


theorem mpd_leftReach_barrier_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (hadj : (hypercubicLattice 2).Adj p q)
    (hbd : bdEdge (mpd_leftReach ω n) s(p, q))
    (hpbox : p ∈ rect 0 (n + 1) 0 n) (hqbox : q ∈ rect 0 (n + 1) 0 n) :
    dualConfig ω (crossEdge s(p, q)) = true := by
  rw [StatMech.RSW.dualCross_open_iff_closed]
  exact mpd_leftReach_boundary_closed ω n hadj hbd hpbox hqbox


theorem mpd_edgeBoundary_nonempty (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) :
    (edgeBoundary 2 (mpd_leftReach ω n)).Nonempty := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hxL : (![0, 0] : Site 2) ∈ leftSide 0 ((m : ℤ) + 1) 0 (m : ℤ) := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨le_refl 0, by positivity, le_refl 0, by positivity⟩
  have hyR : (![(m : ℤ) + 1, 0] : Site 2) ∈ rightSide 0 ((m : ℤ) + 1) 0 (m : ℤ) := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨by positivity, le_refl _, le_refl 0, by positivity⟩
  obtain ⟨w⟩ := jex_lattice_walk_row 0 (m + 1)
  have hw : (hypercubicLattice 2).Walk (![0, 0] : Site 2) (![((m : ℤ) + 1), 0]) := by
    have he : (![((m + 1 : ℕ) : ℤ), 0] : Site 2) = (![(m : ℤ) + 1, 0] : Site 2) := by
      funext i; fin_cases i <;> simp
    rw [he] at w; exact w
  exact edgeBoundary_nonempty_of_walk (mpd_leftReach ω (m : ℤ)) hw
    (mpd_leftSide_subset_leftReach ω (m : ℤ) hxL)
    (mpd_rightSide_notin_leftReach ω (m : ℤ) hnoH hyR)


theorem mpd_exists_dualCircuit (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (mpd_leftReach ω n)).Walk u u), c.IsCycle := by
  obtain ⟨⟨a, b⟩, hab⟩ := mpd_edgeBoundary_nonempty ω hn hnoH
  exact exists_dualCircuit_of_finite_of_edgeBoundary (mpd_leftReach ω n)
    (mpd_leftReach_finite ω n) hab


end Universality
end StatMech
