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
import Def.StatisticalMechanics.Code.Lattice.KingNoSeparationClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem kns_exists_lexMin_escape {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} {z : Site 2} (hzI : z ∈ jil_offSupportInterior Vc) (hznT : z ∉ T)
    (M : ℤ) :
    ∃ q ∈ jil_offSupportInterior Vc, q ∉ T ∧
      ∀ w ∈ jil_offSupportInterior Vc, w ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M w := by
  classical
  have hfin := rlc_offSupportInterior_finite Vc
  set S : Finset (Site 2) := hfin.toFinset.filter (fun w => w ∉ T) with hS
  have hzS : z ∈ S := by
    rw [hS, Finset.mem_filter]; exact ⟨hfin.mem_toFinset.mpr hzI, hznT⟩
  obtain ⟨q, hqS, hqmin⟩ := S.exists_min_image (rlc_lexMeasure M) ⟨z, hzS⟩
  rw [hS, Finset.mem_filter] at hqS
  refine ⟨q, hfin.mem_toFinset.mp hqS.1, hqS.2, ?_⟩
  intro w hwI hwnT
  exact hqmin w (by rw [hS, Finset.mem_filter]; exact ⟨hfin.mem_toFinset.mpr hwI, hwnT⟩)


theorem kns_kingSeparation_escape_structure {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsep : kns_KingSeparation Vc seed) :
    ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧
      ∃ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧
        (∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
          rlc_lexMeasure M q ≤ rlc_lexMeasure M z) ∧
        (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧
        (![q 0, q 1 - 1] : Site 2) ∈ Vc.support := by
  obtain ⟨T, hseedT, hTsub, hsat, z, hzI, hznT⟩ := hsep
  obtain ⟨M₀, hM₀⟩ := rlc_interior_bounded Vc
  set M : ℤ := M₀ + 1 with hM
  obtain ⟨q, hqI, hqnT, hmin⟩ := kns_exists_lexMin_escape Vc hzI hznT M
  
  have hqL : q ∈ jec_leftRegion Vc := (jil_mem_offSupportInterior Vc _ |>.mp hqI).2
  obtain ⟨⟨hq0a, hq0b⟩, ⟨hq1a, hq1b⟩⟩ := hM₀ _ hqL
  have hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hWbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hSbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  obtain ⟨hW, hSsup⟩ :=
    kns_escape_axials_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox hWbox hSbox
  exact ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hSsup⟩


theorem kns_noKingSeparation_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : kns_EscapeThickPoint Vc seed) :
    ksc_NoKingSeparation Vc seed := by
  by_contra hns
  have hsep := (kns_kingSeparation_iff_not_noKingSeparation Vc hseedI).mpr hns
  obtain ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hSsup⟩ :=
    kns_kingSeparation_escape_structure Vc hsep
  have htp := hres T hseedT hTsub hsat M q hqI hqnT hmin hW hSsup
  exact (kns_thickPoint_iff_not_fourThin Vc).mp htp hthin


theorem kns_escapeThickPoint_of_noKingSeparation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hns : ksc_NoKingSeparation Vc seed) :
    kns_EscapeThickPoint Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hW _hSsup
  exact absurd (hns T hseedT hTsub hsat hqI) hqnT


theorem kns_kingRowLinked_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : kns_EscapeThickPoint Vc seed) :
    mci_KingRowLinked Vc seed :=
  ksc_kingRowLinked_of_noKingSeparation Vc hseedI
    (kns_noKingSeparation_of_fourThin Vc hseedI hthin hres)


theorem kns_kingInteriorConnected_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : ∀ seed ∈ jil_offSupportInterior Vc, kns_EscapeThickPoint Vc seed) :
    mci_KingInteriorConnected Vc :=
  ⟨z₀, hz₀, kns_kingRowLinked_of_fourThin Vc hz₀ hthin (hres z₀ hz₀)⟩


theorem kns_fjord_thickPoint : kns_ThickPoint sdc_fjord := by
  refine ⟨(![3, 1] : Site 2), (![4, 1] : Site 2), mci_fjord_on_31, sdc_fjord_on_41, ?_,
    mci_fjord_no_row1_horizontal_edge⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide


theorem kns_fjord_kingSeparation : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) := by
  obtain ⟨hRPint, hRPsat, hRPproper⟩ := ksc_fjord_rp_is_king_separation
  exact ⟨iwc_RightPocket, iwc_mem_rightPocket_51, hRPint, hRPsat,
    (![1, 1] : Site 2), sdc_fjord_mem_interior_11,
    fun h => iwc_not_rightPocket_11 h⟩


theorem kns_fjord_escapeThickPoint : kns_EscapeThickPoint sdc_fjord (![5, 1] : Site 2) :=
  fun _ _ _ _ _ _ _ _ _ _ _ => kns_fjord_thickPoint


theorem kns_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    kns_EscapeThickPoint sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, kns_fjord_escapeThickPoint,
   mci_fjord_not_fourThin⟩


theorem kns_ksd_escapeThickPoint : kns_EscapeThickPoint ksd_stair (![1, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin hW hSsup
  
  exact absurd (ksc_ksd_noKingSeparation T hseedT hTsub hsat hqI) hqnT


theorem kns_kda_escapeThickPoint : kns_EscapeThickPoint kda_stairDR (![3, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin hW hSsup
  exact absurd (ksc_kda_noKingSeparation T hseedT hTsub hsat hqI) hqnT

end Lattice
end StatMech
