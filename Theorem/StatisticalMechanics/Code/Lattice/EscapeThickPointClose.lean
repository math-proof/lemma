/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean -/

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
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem etp_adj_vert (x y : ℤ) :
    (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x, y + 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp


theorem etp_adj_horiz (x y : ℤ) :
    (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x + 1, y] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp


theorem etp_horiz_wall_upperGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hL : (![x - 1, y] : Site 2) ∈ T)
    (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hRnT : (![x + 1, y] : Site 2) ∉ T) :
    (![x, y + 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hUI
  
  have hUT : (![x, y + 1] : Site 2) ∈ T := by
    have h : (![(x - 1) + 1, y + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hL (by simpa using hUI)
    simpa using h
  
  have hRT : (![x + 1, y] : Site 2) ∈ T := by
    have h : (![x + 1, (y + 1) + (-1)] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inr rfl) hUT (by simpa using hR)
    simpa using h
  exact hRnT hRT


theorem etp_horiz_wall_lowerGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hL : (![x - 1, y] : Site 2) ∈ T)
    (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hRnT : (![x + 1, y] : Site 2) ∉ T) :
    (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hDI
  have hDT : (![x, y - 1] : Site 2) ∈ T := by
    have h : (![(x - 1) + 1, y + (-1)] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inr rfl) hL (by simpa using hDI)
    simpa using h
  have hRT : (![x + 1, y] : Site 2) ∈ T := by
    have h : (![x + 1, (y - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hDT (by simpa using hR)
    simpa using h
  exact hRnT hRT


theorem etp_horiz_wall_gaps_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {x y : ℤ} (hL : (![x - 1, y] : Site 2) ∈ T)
    (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hRnT : (![x + 1, y] : Site 2) ∉ T) :
    (![x, y] : Site 2) ∈ Vc.support ∧
      (![x, y + 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
      (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc :=
  ⟨ksc_separated_midOnSupport_horiz Vc hsat hTsub hL hR hRnT,
   etp_horiz_wall_upperGap_blocked Vc hsat hL hR hRnT,
   etp_horiz_wall_lowerGap_blocked Vc hsat hL hR hRnT⟩


theorem etp_thickPoint_of_swCorner {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {q : Site 2}
    (hW : (![q 0 - 1, q 1] : Site 2) ∈ Vc.support)
    (hS : (![q 0, q 1 - 1] : Site 2) ∈ Vc.support)
    (hC : (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support)
    (hnon : s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∉ Vc.edges ∨
            s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc := by
  rcases hnon with h | h
  · 
    refine ⟨(![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2), hW, hC, ?_, h⟩
    have hadj := (etp_adj_vert (q 0 - 1) (q 1 - 1)).symm
    rw [show ((q 1 - 1) + 1 : ℤ) = q 1 by ring] at hadj
    exact hadj
  · 
    refine ⟨(![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2), hS, hC, ?_, h⟩
    have hadj := (etp_adj_horiz (q 0 - 1) (q 1 - 1)).symm
    rw [show ((q 0 - 1) + 1 : ℤ) = q 0 by ring] at hadj
    exact hadj


theorem etp_swCorner_dichotomy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hCbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc :=
  kns_lexBelow_diag_corner Vc hsat hTsub hqI hqnT M hmin hqbox hCbox


end Lattice
end StatMech
