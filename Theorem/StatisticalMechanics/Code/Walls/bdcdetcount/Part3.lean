/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdcdetcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfctfinitecount.Part4
import Theorem.StatisticalMechanics.Code.Walls.bsgspantreegn
import Def.StatisticalMechanics.Code.Walls.bdcdetcount.Part3
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

theorem bdc_cut_transport (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j w₁ w₂ : Site 2)
    (h : ¬ (bkg_deleteVertex (bgf2_Gf (bdc_shiftCfg (bgf2_centre L j) ω) L) 0).Reachable w₁ w₂) :
    ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable
        (w₁ + bgf2_centre L j) (w₂ + bgf2_centre L j) := by
  intro hr
  apply h
  have hm := hr.map (bdc_delHom L ω j)
  have e1 : (bdc_delHom L ω j) (w₁ + bgf2_centre L j) = w₁ := add_sub_cancel_right _ _
  have e2 : (bdc_delHom L ω j) (w₂ + bgf2_centre L j) = w₂ := add_sub_cancel_right _ _
  rw [e1, e2] at hm; exact hm


theorem bdc_trif_separation_at (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j : Site 2)
    (h : bao_AllOpenTrif (bdc_shiftCfg (bgf2_centre L j) ω) L) :
    ∃ w₁ w₂ w₃ : Site 2,
      w₁ ≠ bgf2_centre L j ∧ w₂ ≠ bgf2_centre L j ∧ w₃ ≠ bgf2_centre L j ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₂ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₃ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₂ w₃ := by
  set c := bgf2_centre L j with hc
  obtain ⟨w₁, w₂, w₃, hn₁, hn₂, hn₃, hs₁₂, hs₁₃, hs₂₃⟩ := bgf2_trif_separation h
  have hne : ∀ w : Site 2, w ≠ 0 → w + c ≠ c := by
    intro w hw heq
    have : w + c = 0 + c := by rw [zero_add]; exact heq
    exact hw (add_right_cancel this)
  exact ⟨w₁ + c, w₂ + c, w₃ + c, hne _ hn₁, hne _ hn₂, hne _ hn₃,
    bdc_cut_transport L ω j w₁ w₂ hs₁₂,
    bdc_cut_transport L ω j w₁ w₃ hs₁₃,
    bdc_cut_transport L ω j w₂ w₃ hs₂₃⟩


theorem bdc_shiftCfg_zero (ω : ConfigSpace (Sym2 (Site 2))) : bdc_shiftCfg 0 ω = ω := by
  funext e
  simp only [bdc_shiftCfg, add_zero]
  congr 1
  refine e.ind ?_
  intro x y
  simp only [Sym2.map_pair_eq, add_zero]


theorem bdc_trif_separation_at_zero (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2)))
    (h : bao_AllOpenTrif ω L) :
    ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0 ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₂ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₃ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₂ w₃ :=
  bgf2_trif_separation h


theorem bdc_hub_feed (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j : Site 2)
    (h : bao_AllOpenTrif (bdc_shiftCfg (bgf2_centre L j) ω) L)
    {S : Finset (Site 2)} (hcS : bgf2_centre L j ∈ S)
    (hmem : ∀ w₁ w₂ w₃ : Site 2, w₁ ≠ bgf2_centre L j → w₂ ≠ bgf2_centre L j → w₃ ≠ bgf2_centre L j →
      w₁ ∈ S ∧ w₂ ∈ S ∧ w₃ ∈ S) :
    ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ (⟨bgf2_centre L j, hcS⟩ : {v // v ∈ S}) ∧
      a₂ ≠ ⟨bgf2_centre L j, hcS⟩ ∧ a₃ ≠ ⟨bgf2_centre L j, hcS⟩ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (a₁ : Site 2) (a₂ : Site 2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (a₁ : Site 2) (a₃ : Site 2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (a₂ : Site 2) (a₃ : Site 2) := by
  obtain ⟨w₁, w₂, w₃, hne₁, hne₂, hne₃, hcut₁₂, hcut₁₃, hcut₂₃⟩ := bdc_trif_separation_at L ω j h
  obtain ⟨hm₁, hm₂, hm₃⟩ := hmem w₁ w₂ w₃ hne₁ hne₂ hne₃
  exact bfct_hub_cut_of_separation (G := bgf2_Gf ω L) ⟨bgf2_centre L j, hcS⟩ hm₁ hm₂ hm₃
    hne₁ hne₂ hne₃ hcut₁₂ hcut₁₃ hcut₂₃


theorem bdc_status :
    
    (∀ L : ℕ, 1 ≤ L → ¬ (bgf2_Gf bdc_allOpenCfg L ≤ hypercubicLattice 2)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j : Site 2),
      bao_AllOpenTrif (bdc_shiftCfg (bgf2_centre L j) ω) L →
      ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ bgf2_centre L j ∧ w₂ ≠ bgf2_centre L j ∧ w₃ ≠ bgf2_centre L j ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₂ ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₃ ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₂ w₃) := by
  refine ⟨fun L hL => bdc_Gf_not_le_lattice hL, ?_, ?_⟩
  · intro ω L R h; exact bdc_datum_implies_count ω L R h
  · intro L ω j h; exact bdc_trif_separation_at L ω j h


end StatMech.Walls
