/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean -/

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
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem ewt_escapeRow_notMem_of_run {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqnT : q ∉ T)
    {lo hi x₁ : ℤ}
    (hloff : (![lo, q 1] : Site 2) ∉ Vc.support)
    (hlolo : lo ≤ q 0) (hqhi : q 0 ≤ hi) (hx₁lo : lo ≤ x₁) (hx₁hi : x₁ ≤ hi)
    (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∉ Vc.support) :
    (![x₁, q 1] : Site 2) ∉ T := by
  intro hx₁T
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  apply hqnT
  rw [hq01]
  exact kns_row_complete Vc hsat hTsub hx₁T hloff hx₁lo hx₁hi hlolo hqhi hrun


theorem ewt_escapeRow_down_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {q : Site 2}
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    {wx : ℤ}
    (hw : (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hwnT : (![wx, q 1] : Site 2) ∉ T)
    (hwbox : (-M < wx ∧ wx ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![wx, q 1 - 1] : Site 2) ∈ Vc.support := by
  by_contra hoff
  
  have hdI : (![wx, q 1 - 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    have := rlc_down_mem_interior Vc hw (by simpa using hoff)
    simpa using this
  
  
  have hdT : (![wx, q 1 - 1] : Site 2) ∈ T := by
    by_contra hdnT
    have hle := hmin _ hdI hdnT
    have hlt : rlc_lexMeasure M (![wx, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hwbox.1.1) (by simpa using hwbox.1.2)
        (by simpa using hwbox.2.1) (by simpa using hwbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  
  
  have hadj : (hypercubicLattice 2).Adj (![wx, q 1 - 1] : Site 2) (![wx, q 1] : Site 2) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  exact hwnT (ksc_saturated_axial Vc hsat hdT hw hadj)


theorem ewt_runBottom_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hq1box : -M < q 1 - 1 ∧ q 1 - 1 ≤ M)
    {lo hi : ℤ}
    (hloff : (![lo, q 1] : Site 2) ∉ Vc.support)
    (hlolo : lo ≤ q 0) (hqhi : q 0 ≤ hi)
    (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∉ Vc.support)
    (hrunI : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
    {x : ℤ} (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hxbox : -M < x ∧ x ≤ M) :
    (![x, q 1 - 1] : Site 2) ∈ Vc.support := by
  have hxI : (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc := hrunI x hxlo hxhi
  have hxnT : (![x, q 1] : Site 2) ∉ T :=
    ewt_escapeRow_notMem_of_run Vc hsat hTsub hqnT hloff hlolo hqhi hxlo hxhi hrun
  exact ewt_escapeRow_down_onSupport Vc hsat M hmin hqbox hxI hxnT ⟨hxbox, hq1box⟩


theorem ewt_vert_wall_rightGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hD : (![x, y - 1] : Site 2) ∈ T)
    (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hUnT : (![x, y + 1] : Site 2) ∉ T) :
    (![x + 1, y] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hRI
  have hRT : (![x + 1, y] : Site 2) ∈ T := by
    have h : (![x + 1, (y - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hD (by simpa using hRI)
    simpa using h
  have hUT : (![x, y + 1] : Site 2) ∈ T := by
    have h : (![(x + 1) + (-1), y + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inr rfl) (Or.inl rfl) hRT (by simpa using hU)
    simpa using h
  exact hUnT hUT


theorem ewt_vert_wall_leftGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hD : (![x, y - 1] : Site 2) ∈ T)
    (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hUnT : (![x, y + 1] : Site 2) ∉ T) :
    (![x - 1, y] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hLI
  have hLT : (![x - 1, y] : Site 2) ∈ T := by
    have h : (![x + (-1), (y - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inr rfl) (Or.inl rfl) hD (by simpa using hLI)
    simpa using h
  have hUT : (![x, y + 1] : Site 2) ∈ T := by
    have h : (![(x - 1) + 1, y + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hLT (by simpa using hU)
    simpa using h
  exact hUnT hUT


theorem ewt_vert_wall_gaps_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {x y : ℤ} (hD : (![x, y - 1] : Site 2) ∈ T)
    (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hUnT : (![x, y + 1] : Site 2) ∉ T) :
    (![x, y] : Site 2) ∈ Vc.support ∧
      (![x + 1, y] : Site 2) ∉ jil_offSupportInterior Vc ∧
      (![x - 1, y] : Site 2) ∉ jil_offSupportInterior Vc :=
  ⟨ksc_separated_midOnSupport_vert Vc hsat hTsub hD hU hUnT,
   ewt_vert_wall_rightGap_blocked Vc hsat hD hU hUnT,
   ewt_vert_wall_leftGap_blocked Vc hsat hD hU hUnT⟩


end Lattice
end StatMech
