/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.GlobalThickPointClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem cat_thickPoint_of_seCorner {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {e y : ℤ}
    (hE : (![e, y] : Site 2) ∈ Vc.support)
    (hB : (![e - 1, y - 1] : Site 2) ∈ Vc.support)
    (hC : (![e, y - 1] : Site 2) ∈ Vc.support)
    (hnon : s((![e, y] : Site 2), (![e, y - 1] : Site 2)) ∉ Vc.edges ∨
            s((![e - 1, y - 1] : Site 2), (![e, y - 1] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc := by
  rcases hnon with h | h
  · 
    refine ⟨(![e, y] : Site 2), (![e, y - 1] : Site 2), hE, hC, ?_, h⟩
    have hadj := (etp_adj_vert e (y - 1)).symm
    rw [show ((y - 1) + 1 : ℤ) = y by ring] at hadj
    exact hadj
  · 
    refine ⟨(![e - 1, y - 1] : Site 2), (![e, y - 1] : Site 2), hB, hC, ?_, h⟩
    have hadj := etp_adj_horiz (e - 1) (y - 1)
    rw [show ((e - 1) + 1 : ℤ) = e by ring] at hadj
    exact hadj


theorem cat_seCorner_dichotomy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {q : Site 2} (M e : ℤ)
    (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hCbox : (-M < e ∧ e ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M))
    (hwI : (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hwnT : (![e - 1, q 1] : Site 2) ∉ T) :
    (![e, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCoff, hCI⟩ := hcon
  
  have hCT : (![e, q 1 - 1] : Site 2) ∈ T := by
    by_contra hCnT
    have hle := hmin _ hCI hCnT
    have hlt : rlc_lexMeasure M (![e, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hCbox.1.1) (by simpa using hCbox.1.2)
        (by simpa using hCbox.2.1) (by simpa using hCbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  
  have hwT : (![e - 1, q 1] : Site 2) ∈ T := by
    have h : (![e + (-1), (q 1 - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inr rfl) (Or.inl rfl) hCT (by simpa using hwI)
    simpa using h
  exact hwnT hwT


theorem cat_runEnd_corner_data {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (M : ℤ) (hqnT : q ∉ T)
    (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hq1box : -M < q 1 - 1 ∧ q 1 - 1 ≤ M)
    {e : ℤ} (he₁ : q 0 < e) (heM : -M < e - 1 ∧ e - 1 ≤ M)
    (he₃ : ∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc) :
    (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc ∧
      (![e - 1, q 1] : Site 2) ∉ T ∧
      (![e - 1, q 1 - 1] : Site 2) ∈ Vc.support := by
  have hlastI : (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc :=
    he₃ (e - 1) (by omega) (by omega)
  have hrun_off : ∀ t : ℤ, q 0 ≤ t → t ≤ e - 1 → (![t, q 1] : Site 2) ∉ Vc.support := by
    intro t ht ht'; exact (jil_mem_offSupportInterior Vc _ |>.mp (he₃ t ht (by omega))).1
  have hlastnT : (![e - 1, q 1] : Site 2) ∉ T :=
    ewt_escapeRow_notMem_of_run Vc hsat hTsub hqnT
      (hrun_off (q 0) (le_refl _) (by omega)) (le_refl _) (by omega)
      (by omega) (le_refl _) hrun_off
  have hbot : (![e - 1, q 1 - 1] : Site 2) ∈ Vc.support :=
    ewt_escapeRow_down_onSupport Vc hsat M hmin hqbox hlastI hlastnT ⟨heM, hq1box⟩
  exact ⟨hlastI, hlastnT, hbot⟩


end Lattice
end StatMech
