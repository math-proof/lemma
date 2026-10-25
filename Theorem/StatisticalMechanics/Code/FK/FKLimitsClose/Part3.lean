/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Def.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


theorem flc_transBoxMass_eq (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) :
    lmc_transBoxMass v N t p m hNm
      = med_multiMassProb
          (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
          (flc_transEdges v N t m hNm) := rfl


theorem flc_valImage_transEdges (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (m : ℕ) (hNm : N ≤ m) :
    (flc_transEdges v N t m hNm).image
        (Sym2.map (Subtype.val : fvs_transBoxVerts d m v → Site d))
      = (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e) := by
  unfold flc_transEdges
  
  rw [show (Sym2.map (Subtype.val : fvs_transBoxVerts d m v → Site d))
        = lmc_transEdgeIncl d m v from rfl]
  rw [lmc_transImage_eq_smulImage d m v (t.image (innerEdgeLE d hNm))]
  congr 1
  rw [Finset.image_image]
  refine Finset.image_congr (fun eb _ => ?_)
  exact med_edgeIncl_innerEdgeLE N m hNm eb


theorem flc_centred_med_eq_measure (n : ℕ) (tb : Finset (Sym2 (boxVerts d n))) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    med_multiMassProb
        (wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d))
          (boxBoundary d n) p 2) tb
      = (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (tb.image (edgeIncl d n))) :=
  (med_centred_mass_eq n tb hp hp1).symm


theorem flc_squeeze_lower (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hNm : N ≤ m) (hm : 1 ≤ m) :
    (wiredFiniteMeasure d (m + flc_vrad v + 1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e => (Multiplicative.ofAdd v) • e)))
      ≤ lmc_transBoxMass v N t p m hNm := by
  set c := flc_vrad v with hc
  have hsub : fvs_transBox d m v ⊆ box d (m + c + 1) :=
    (flc_transBox_subset_box v m).trans (box_mono d (by omega))
  
  have hdom := ocd_latticeWired_multiMass_dominated (Sin := fvs_transBox d m v)
    (Sout := box d (m + c + 1)) (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    (boxBoundary d (m + c + 1)) (fvs_transBoxBoundary d m v)
    (flc_hmargin_transBox_in_box v hsub)
    (flc_hbdryIn_transBox hm v)
    hp hp1 (by norm_num : (1:ℝ) ≤ 2) (flc_transEdges v N t m hNm)
  
  rw [flc_transBoxMass_eq v N t p m hNm]
  refine le_trans ?_ hdom
  
  rw [show (boxBoundary d (m + c + 1)) = (boxBoundary d (m + c + 1)) from rfl]
  rw [flc_centred_med_eq_measure (m + c + 1) (flc_transEdges v N t m hNm |>.image
        (ocd_innerEdge (flc_incl hsub))) hp hp1]
  
  apply le_of_eq
  congr 2
  rw [show (edgeIncl d (m + c + 1))
        = (Sym2.map (Subtype.val : boxVerts d (m + c + 1) → Site d)) from rfl,
    flc_valImage_ocd_innerEdge_image hsub (flc_transEdges v N t m hNm),
    flc_valImage_transEdges v N t m hNm]


theorem flc_squeeze_upper (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m a : ℕ) (hNm : N ≤ m) (ha : 1 ≤ a)
    (hcond : a + flc_vrad v + 1 ≤ m)
    (tb_a : Finset (Sym2 (boxVerts d a)))
    (htb : tb_a.image (edgeIncl d a)
      = (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)) :
    lmc_transBoxMass v N t p m hNm
      ≤ (wiredFiniteMeasure d a hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
              (fun e => (Multiplicative.ofAdd v) • e))) := by
  set c := flc_vrad v with hc
  have hsub : box d a ⊆ fvs_transBox d m v :=
    flc_box_subset_transBox v (by omega : a + flc_vrad v ≤ m)
  
  have hdom := ocd_latticeWired_multiMass_dominated (Sin := box d a)
    (Sout := fvs_transBox d m v) (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    (fvs_transBoxBoundary d m v) (boxBoundary d a)
    (flc_hmargin_box_in_transBox v hsub (by omega))
    (flc_hbdryIn_box ha)
    hp hp1 (by norm_num : (1:ℝ) ≤ 2) tb_a
  
  have hkey : tb_a.image (ocd_innerEdge (flc_incl hsub)) = flc_transEdges v N t m hNm := by
    apply flc_image_eq_of_val_image_eq
    rw [flc_valImage_transEdges v N t m hNm,
      flc_valImage_ocd_innerEdge_image hsub tb_a,
      show (Sym2.map (Subtype.val : boxVerts d a → Site d)) = edgeIncl d a from rfl, htb]
  rw [flc_transBoxMass_eq v N t p m hNm, ← hkey]
  refine le_trans hdom ?_
  
  rw [flc_centred_med_eq_measure a tb_a hp hp1, htb]


theorem flc_transBoxMass_tendsto_translated_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m' : ℕ => lmc_transBoxMass v N t p (N + m') (Nat.le_add_right N m')) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e => (Multiplicative.ofAdd v) • e))))) := by
  classical
  set c := flc_vrad v with hc
  set vs := (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e) with hvs
  
  obtain ⟨N', t', hvs'⟩ := cdc_finset_in_box vs
  set L := (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs) with hL
  
  have hbase : Tendsto (fun r => (wiredFiniteMeasure d r hp hp1 (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    have h := med_centred_tendsto_iv N' t' hp hp1
    rw [← hvs'] at h
    
    rw [hL]
    exact h
  
  have hlowtends : Tendsto (fun m' : ℕ =>
      (wiredFiniteMeasure d ((N + m') + c + 1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    refine hbase.comp ?_
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun m' hm' => by omega⟩
  
  have huptends : Tendsto (fun m' : ℕ =>
      (wiredFiniteMeasure d ((N + m') - c - 1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    refine hbase.comp ?_
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b + N + c + 1, fun m' hm' => by omega⟩
  
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowtends huptends ?_ ?_
  · 
    filter_upwards [Filter.eventually_ge_atTop 1] with m' hm'
    have hm : 1 ≤ N + m' := by omega
    exact flc_squeeze_lower v N t hp hp1 (N + m') (Nat.le_add_right N m') hm
  · 
    filter_upwards [Filter.eventually_ge_atTop (N' + c + 2)] with m' hm'
    
    have hNa : N' ≤ (N + m') - c - 1 := by omega
    have ha : 1 ≤ (N + m') - c - 1 := by omega
    have hcond : ((N + m') - c - 1) + flc_vrad v + 1 ≤ (N + m') := by rw [← hc]; omega
    have htb : (t'.image (innerEdgeLE d hNa)).image (edgeIncl d ((N + m') - c - 1)) = vs := by
      have h1 : (t'.image (innerEdgeLE d hNa)).image (edgeIncl d ((N + m') - c - 1))
          = t'.image (edgeIncl d N') := by
        rw [Finset.image_image]
        exact Finset.image_congr (fun eb _ => edgeIncl_innerEdgeLE d hNa eb)
      rw [h1, hvs']
    exact flc_squeeze_upper v N t hp hp1 (N + m') ((N + m') - c - 1)
      (Nat.le_add_right N m') ha hcond (t'.image (innerEdgeLE d hNa)) htb


theorem flc_wiredPlacement {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : Multiplicative (Site d)) :
    lmc_wiredPlacement hp hp1 g := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, hst, ?_⟩
  
  have hmatch : s.image (fun e => g⁻¹ • e)
      = (t.image (edgeIncl d N)).image
          (fun e => (Multiplicative.ofAdd (Multiplicative.toAdd g⁻¹)) • e) := by
    rw [hst]
    simp only [ofAdd_toAdd]
  rw [hmatch]
  exact flc_transBoxMass_tendsto_translated_iv (Multiplicative.toAdd g⁻¹) N t hp hp1


theorem flc_wiredPlacement_forall {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∀ g : Multiplicative (Site d), lmc_wiredPlacement hp hp1 g :=
  fun g => flc_wiredPlacement hp hp1 g


theorem flc_wiredMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) :
    cdc_wiredMultiHomogeneous hp hp1 g :=
  lmc_wiredMultiHomogeneous hp hp1 g (flc_wiredPlacement hp hp1 g)


theorem flc_wiredIV_isTranslationInvariant {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  lmc_wiredIV_isTranslationInvariant_of_placement hp hp1 (flc_wiredPlacement_forall hp hp1)

end FK
end StatMech
