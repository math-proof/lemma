/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfinfinalclose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
import Def.StatisticalMechanics.Code.Walls.bscsupercut.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

#check @bfin_SuperCutBridge


theorem bsc_siteConn_of_superReach {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y) (hint : bsc_BoxesInternallyConnected ω L y)
    {a b : Site d} (ha : bgn_idx L a ≠ bgn_idx L y) (hb : bgn_idx L b ≠ bgn_idx L y)
    (h : (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable (bgn_idx L a) (bgn_idx L b)) :
    Connected d (removeSites (bc61_boxAround d L y) ω) a b := by
  obtain ⟨p⟩ := h
  
  have key : ∀ {j k : Site d}
      (p : (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Walk j k),
      ∀ a' b', bgn_idx L a' = j → bgn_idx L b' = k →
        j ≠ bgn_idx L y → k ≠ bgn_idx L y →
        Connected d (removeSites (bc61_boxAround d L y) ω) a' b' := by
    intro j k p
    induction p with
    | nil =>
      intro a' b' ha' hb' hjne hkne
      
      exact hint a' b' (ha'.trans hb'.symm) (by rw [ha']; exact hjne)
    | @cons j z k hadj q ih =>
      intro a' b' ha' hb' hjne hkne
      obtain ⟨hbgnadj, hjne', hzne⟩ := hadj
      obtain ⟨_, c, e, hc, he, hce⟩ := hbgnadj
      
      have hac : Connected d (removeSites (bc61_boxAround d L y) ω) a' c :=
        hint a' c (ha'.trans hc.symm) (by rw [ha']; exact hjne)
      
      have hcout : c ∉ bc61_boxAround d L y := fun hcbox => hjne (hc ▸ (hy c).mp hcbox)
      have heout : e ∉ bc61_boxAround d L y := fun hebox => hzne (he ▸ (hy e).mp hebox)
      have hce_conn : Connected d (removeSites (bc61_boxAround d L y) ω) c e :=
        bc61_cut_adj_connected hce.1 hce.2 hcout heout
      
      have heb : Connected d (removeSites (bc61_boxAround d L y) ω) e b' := ih e b' he hb' hzne hkne
      exact (hac.trans hce_conn).trans heb
  exact key p a b rfl rfl ha hb


theorem bsc_super_disconnected {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y) (hint : bsc_BoxesInternallyConnected ω L y)
    {a b : Site d} (ha : bgn_idx L a ≠ bgn_idx L y) (hb : bgn_idx L b ≠ bgn_idx L y)
    (hdis : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a b) :
    ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable (bgn_idx L a) (bgn_idx L b) :=
  fun hr => hdis (bsc_siteConn_of_superReach hy hint ha hb hr)


theorem bsc_bridge_of_internalConn {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y) (hint : bsc_BoxesInternallyConnected ω L y)
    (htri : bc67_IsGnTrifurcation ω L y) :
    ∃ w₁ w₂ w₃ : Site d,
      w₁ ≠ bgn_idx L y ∧ w₂ ≠ bgn_idx L y ∧ w₃ ≠ bgn_idx L y ∧
      (bgn_Gn ω L).Adj (bgn_idx L y) w₁ ∧ (bgn_Gn ω L).Adj (bgn_idx L y) w₂ ∧
      (bgn_Gn ω L).Adj (bgn_idx L y) w₃ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₂ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₃ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₂ w₃ ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₁).Infinite ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₂).Infinite ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₃).Infinite := by
  obtain ⟨a₁, a₂, a₃, ⟨hi₁, hi₂, hi₃⟩, ⟨hf₁, hf₂, hf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩ := htri
  
  have hd₁₂ : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ := hcut₁₂
  have hd₁₃ : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ := hcut₁₃
  have hd₂₃ : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃ := hcut₂₃
  obtain ⟨hne₁, hadj₁⟩ := bsc_hub_adj_armImage hy hi₁ hf₁
  obtain ⟨hne₂, hadj₂⟩ := bsc_hub_adj_armImage hy hi₂ hf₂
  obtain ⟨hne₃, hadj₃⟩ := bsc_hub_adj_armImage hy hi₃ hf₃
  refine ⟨bgn_idx L a₁, bgn_idx L a₂, bgn_idx L a₃, hne₁, hne₂, hne₃,
    hadj₁, hadj₂, hadj₃, ?_, ?_, ?_,
    bsc_arm_ray_infinite hy hf₁, bsc_arm_ray_infinite hy hf₂, bsc_arm_ray_infinite hy hf₃⟩
  · exact bsc_super_disconnected hy hint hne₁ hne₂ hd₁₂
  · exact bsc_super_disconnected hy hint hne₁ hne₃ hd₁₃
  · exact bsc_super_disconnected hy hint hne₂ hne₃ hd₂₃


theorem bsc_bfin_SuperCutBridge_of_hyp (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ)
    (H : ∀ y : Site 2, bc67_IsGnTrifurcation ω L y →
      bsc_IsBoxCentre L y ∧ bsc_BoxesInternallyConnected ω L y) :
    bfin_SuperCutBridge ω L := by
  intro y htri
  obtain ⟨hy, hint⟩ := H y htri
  exact bsc_bridge_of_internalConn hy hint htri

#check @bsc_siteConn_of_superReach
#check @bsc_bfin_SuperCutBridge_of_hyp


theorem bsc_upperLines_forward {L : ℕ} (hL : 3 ≤ L) :
    ∃ w₁ w₂ w₃ : Site 2,
      (w₁ ≠ bgn_idx L (0 : Site 2) ∧ w₂ ≠ bgn_idx L (0 : Site 2) ∧ w₃ ≠ bgn_idx L (0 : Site 2)) ∧
      ((bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₁ ∧
       (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₂ ∧
       (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₃) ∧
      ((ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₁).Infinite ∧
       (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₂).Infinite ∧
       (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₃).Infinite) := by
  have hy := bsc_boxCentre_zero 2 L
  obtain ⟨a₁, a₂, a₃, ⟨hi₁, hi₂, hi₃⟩, ⟨hf₁, hf₂, hf₃⟩, _⟩ :=
    bc67_upperLines_is_G_n_trifurcation hL
  obtain ⟨hne₁, hadj₁⟩ := bsc_hub_adj_armImage hy hi₁ hf₁
  obtain ⟨hne₂, hadj₂⟩ := bsc_hub_adj_armImage hy hi₂ hf₂
  obtain ⟨hne₃, hadj₃⟩ := bsc_hub_adj_armImage hy hi₃ hf₃
  exact ⟨bgn_idx L a₁, bgn_idx L a₂, bgn_idx L a₃, ⟨hne₁, hne₂, hne₃⟩,
    ⟨hadj₁, hadj₂, hadj₃⟩,
    ⟨bsc_arm_ray_infinite hy hf₁, bsc_arm_ray_infinite hy hf₂, bsc_arm_ray_infinite hy hf₃⟩⟩

#check @bsc_upperLines_forward


theorem bsc_status {L : ℕ} (hL : 3 ≤ L) :
    
    (∃ w₁ w₂ w₃ : Site 2,
      (w₁ ≠ bgn_idx L (0 : Site 2) ∧ w₂ ≠ bgn_idx L (0 : Site 2) ∧ w₃ ≠ bgn_idx L (0 : Site 2)) ∧
      ((bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₁ ∧
       (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₂ ∧
       (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₃) ∧
      ((ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₁).Infinite ∧
       (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₂).Infinite ∧
       (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₃).Infinite)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))),
      (∀ y : Site 2, bc67_IsGnTrifurcation ω L y →
        bsc_IsBoxCentre L y ∧ bsc_BoxesInternallyConnected ω L y) →
      bfin_SuperCutBridge ω L) := by
  exact ⟨bsc_upperLines_forward hL, fun ω H => bsc_bfin_SuperCutBridge_of_hyp ω L H⟩

#check @bsc_status

end StatMech.Walls
