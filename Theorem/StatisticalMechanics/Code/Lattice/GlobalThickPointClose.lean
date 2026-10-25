/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.KingStepConnectClose
import Theorem.StatisticalMechanics.Code.Lattice.KingNoSeparationClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EscapeThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EscapeWallThickClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem gtp_thickPoint_of_adj_horiz {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (h1 : (![x, y] : Site 2) ∈ Vc.support) (h2 : (![x + 1, y] : Site 2) ∈ Vc.support)
    (hne : s((![x, y] : Site 2), (![x + 1, y] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc := by
  refine ⟨_, _, h1, h2, ?_, hne⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp


theorem gtp_thickPoint_of_adj_vert {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (h1 : (![x, y] : Site 2) ∈ Vc.support) (h2 : (![x, y + 1] : Site 2) ∈ Vc.support)
    (hne : s((![x, y] : Site 2), (![x, y + 1] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc := by
  refine ⟨_, _, h1, h2, ?_, hne⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp


theorem gtp_edge_or_thick_horiz {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (h1 : (![x, y] : Site 2) ∈ Vc.support) (h2 : (![x + 1, y] : Site 2) ∈ Vc.support) :
    s((![x, y] : Site 2), (![x + 1, y] : Site 2)) ∈ Vc.edges ∨ kns_ThickPoint Vc := by
  by_cases he : s((![x, y] : Site 2), (![x + 1, y] : Site 2)) ∈ Vc.edges
  · exact Or.inl he
  · exact Or.inr (gtp_thickPoint_of_adj_horiz Vc h1 h2 he)


theorem gtp_edge_or_thick_vert {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (h1 : (![x, y] : Site 2) ∈ Vc.support) (h2 : (![x, y + 1] : Site 2) ∈ Vc.support) :
    s((![x, y] : Site 2), (![x, y + 1] : Site 2)) ∈ Vc.edges ∨ kns_ThickPoint Vc := by
  by_cases he : s((![x, y] : Site 2), (![x, y + 1] : Site 2)) ∈ Vc.edges
  · exact Or.inl he
  · exact Or.inr (gtp_thickPoint_of_adj_vert Vc h1 h2 he)


theorem gtp_eastBoundary_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {q : Site 2}
    (hqI : q ∈ jil_offSupportInterior Vc) :
    ∃ e : ℤ, q 0 < e ∧ (![e, q 1] : Site 2) ∈ Vc.support ∧
      ∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc := by
  classical
  obtain ⟨M, hM⟩ := rlc_interior_bounded Vc
  
  have hbound : ∃ n : ℕ, (![q 0 + ((n : ℤ) + 1), q 1] : Site 2) ∉ jil_offSupportInterior Vc := by
    refine ⟨(M - q 0 + 1).toNat, ?_⟩
    intro hin
    have hL := (jil_mem_offSupportInterior Vc _ |>.mp hin).2
    have := (hM _ hL).1.2
    simp only [Matrix.cons_val_zero] at this
    omega
  set P : ℕ → Prop := fun n => (![q 0 + ((n : ℤ) + 1), q 1] : Site 2) ∉ jil_offSupportInterior Vc
    with hP
  have hPfind : P (Nat.find hbound) := Nat.find_spec hbound
  set n0 := Nat.find hbound with hn0
  set e : ℤ := q 0 + ((n0 : ℤ) + 1) with he
  have hq01 : q = (![q 0, q 1] : Site 2) := by ext i; fin_cases i <;> simp
  
  have hxint : ∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    intro x hxlo hxhi
    obtain ⟨j, hj⟩ : ∃ j : ℕ, x = q 0 + (j : ℤ) := ⟨(x - q 0).toNat, by omega⟩
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj, hj0]; simp only [Nat.cast_zero, add_zero]; rw [← hq01]; exact hqI
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
      have hkn0 : k < n0 := by omega
      have hnp := Nat.find_min hbound hkn0
      simp only [not_not] at hnp
      have hxe : x = q 0 + ((k : ℤ) + 1) := by rw [hj, hk]; push_cast; ring
      rw [hxe]; exact hnp
  refine ⟨e, by omega, ?_, hxint⟩
  
  by_contra hesup
  apply hPfind
  have he1 : (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc :=
    hxint (e - 1) (by omega) (by omega)
  have hh : (![(e - 1) + 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    apply kns_right_mem_interior Vc he1
    simpa using hesup
  simpa using hh


theorem gtp_runEnd_bottomCorner_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} {q : Site 2} {M e : ℤ}
    (hbottom : ∀ wx : ℤ, (-M < wx ∧ wx ≤ M) →
      (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc →
      (![wx, q 1] : Site 2) ∉ T →
      (![wx, q 1 - 1] : Site 2) ∈ Vc.support)
    (hlastbox : -M < e - 1 ∧ e - 1 ≤ M)
    (hlastI : (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hlastnT : (![e - 1, q 1] : Site 2) ∉ T) :
    (![e - 1, q 1 - 1] : Site 2) ∈ Vc.support :=
  hbottom (e - 1) hlastbox hlastI hlastnT


end Lattice
end StatMech
