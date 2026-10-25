/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean -/

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
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem kns_fourThin_noKingSeparation_examples :
    (mci_FourThin ksd_stair ∧ ksc_NoKingSeparation ksd_stair (![1, 1] : Site 2)) ∧
    (mci_FourThin kda_stairDR ∧ ksc_NoKingSeparation kda_stairDR (![3, 1] : Site 2)) :=
  ⟨⟨ksd_stair_fourThin, ksc_ksd_noKingSeparation⟩,
   ⟨kda_stairDR_fourThin, ksc_kda_noKingSeparation⟩⟩


theorem kns_fjord_not_fourThin_has_separation :
    ¬ mci_FourThin sdc_fjord ∧ ¬ ksc_NoKingSeparation sdc_fjord (![5, 1] : Site 2) :=
  ⟨mci_fjord_not_fourThin, ksc_fjord_noKingSeparation_false⟩


theorem kns_offSupport_neighbor_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z w : Site 2} (hz : z ∈ jil_offSupportInterior Vc)
    (hadj : (hypercubicLattice 2).Adj z w) (hwoff : w ∉ Vc.support) :
    w ∈ jil_offSupportInterior Vc :=
  mci_offSupport_neighbor_interior Vc hz hadj hwoff


theorem kns_lexBelow_axial_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    {w : Site 2} (hwadj : (hypercubicLattice 2).Adj q w)
    (hwbox : (-M < w 0 ∧ w 0 ≤ M) ∧ (-M < w 1 ∧ w 1 ≤ M))
    (hlex : w 1 < q 1 ∨ (w 1 = q 1 ∧ w 0 < q 0)) :
    w ∈ Vc.support := by
  by_contra hwoff
  
  have hwI : w ∈ jil_offSupportInterior Vc :=
    kns_offSupport_neighbor_interior Vc hqI hwadj hwoff
  
  
  have hwT : w ∈ T := by
    by_contra hwnT
    have hle := hmin w hwI hwnT
    have hlt : rlc_lexMeasure M w < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        hwbox.1.1 hwbox.1.2 hwbox.2.1 hwbox.2.2 hlex
    omega
  
  exact hqnT (ksc_saturated_axial Vc hsat hwT hqI hwadj.symm)


theorem kns_escape_axials_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hWbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hSbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧ (![q 0, q 1 - 1] : Site 2) ∈ Vc.support := by
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  constructor
  · 
    refine kns_lexBelow_axial_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox
      (w := (![q 0 - 1, q 1] : Site 2)) ?_ ?_ ?_
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    · simpa using hWbox
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      right; exact ⟨trivial, by omega⟩
  · 
    refine kns_lexBelow_axial_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox
      (w := (![q 0, q 1 - 1] : Site 2)) ?_ ?_ ?_
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    · simpa using hSbox
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      left; omega


theorem kns_lexBelow_diag_corner {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hCbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCoff, hCI⟩ := hcon
  
  have hCnT : (![q 0 - 1, q 1 - 1] : Site 2) ∉ T → False := by
    intro hCnT
    have hle := hmin _ hCI hCnT
    have hlt : rlc_lexMeasure M (![q 0 - 1, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hCbox.1.1) (by simpa using hCbox.1.2)
        (by simpa using hCbox.2.1) (by simpa using hCbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  have hCT : (![q 0 - 1, q 1 - 1] : Site 2) ∈ T := by
    by_contra h; exact hCnT h
  
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  have hdiag : mci_kingGraph.Adj (![q 0 - 1, q 1 - 1] : Site 2) q := by
    rw [hq01]
    have := mci_kingAdj_diag (q 0 - 1) (q 1 - 1) 1 1 (Or.inl rfl) (Or.inl rfl)
    simpa using this
  exact hqnT (hsat _ _ hCT hqI hdiag)


theorem kns_lexBelow_diag_corner_SE {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hCbox : (-M < q 0 + 1 ∧ q 0 + 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 + 1, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![q 0 + 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCoff, hCI⟩ := hcon
  have hCT : (![q 0 + 1, q 1 - 1] : Site 2) ∈ T := by
    by_contra hCnT
    have hle := hmin _ hCI hCnT
    have hlt : rlc_lexMeasure M (![q 0 + 1, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hCbox.1.1) (by simpa using hCbox.1.2)
        (by simpa using hCbox.2.1) (by simpa using hCbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  have hdiag : mci_kingGraph.Adj (![q 0 + 1, q 1 - 1] : Site 2) q := by
    rw [hq01]
    have := mci_kingAdj_diag (q 0 + 1) (q 1 - 1) (-1) 1 (Or.inr rfl) (Or.inl rfl)
    simpa using this
  exact hqnT (hsat _ _ hCT hqI hdiag)


theorem kns_right_mem_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hright : (![x + 1, y] : Site 2) ∉ Vc.support) :
    (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
  have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x + 1, y] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  exact mci_offSupport_neighbor_interior Vc hz hadj hright


theorem kns_row_complete {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {lo hi y x₀ x₁ : ℤ}
    (hx₀T : (![x₀, y] : Site 2) ∈ T)
    (hloff : (![lo, y] : Site 2) ∉ Vc.support)
    (hx₀lo : lo ≤ x₀) (hx₀hi : x₀ ≤ hi) (hx₁lo : lo ≤ x₁) (hx₁hi : x₁ ≤ hi)
    (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ Vc.support) :
    (![x₁, y] : Site 2) ∈ T := by
  obtain ⟨p, hp⟩ := jil_hsegment_reachable_offSupport {p | p ∈ Vc.support}
    (lo := lo) (hi := hi) (y := y) (x₁ := x₀) (x₂ := x₁)
    (by simpa using hloff) hx₀lo hx₀hi hx₁lo hx₁hi
    (by intro t ht ht'; simpa using hrun t ht ht')
  have hp' : ∀ z ∈ p.support, z ∉ Vc.support := by intro z hz; simpa using hp z hz
  have hx₀I : (![x₀, y] : Site 2) ∈ jil_offSupportInterior Vc := hTsub hx₀T
  have hint := mci_offSupport_walk_interior Vc p hp' hx₀I
  have hpk : ∀ w ∈ (p.mapLe mci_hyper_le_king).support, w ∈ jil_offSupportInterior Vc := by
    intro w hw
    rw [SimpleGraph.Walk.support_mapLe_eq_support mci_hyper_le_king p] at hw
    exact hint w hw
  exact ksc_saturated_absorbs_kingWalk Vc hsat (p.mapLe mci_hyper_le_king) hpk hx₀T


end Lattice
end StatMech
