/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DecoupledForestCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Percolation.DecoupledForestCount


namespace StatMech.Percolation

open Set SimpleGraph Finset

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


open Classical in


theorem dfc_Tcount_le_boundary_succ_of_boxOpenForestSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : dfc_BoxOpenForestSucc ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
  classical
  obtain ⟨Vset, hVne, F, _, vx, b, hπ, hacyc, hmin, htriData, hleaf⟩ := h
  set Tf := tfc_trifFinset ω n with hTf
  have hdeg3 : ∀ x, x ∈ box d n → IsTrifurcation d ω x → 3 ≤ F.degree (vx x) := by
    intro x hxbox htri
    obtain ⟨hvx, hreach, hcut⟩ := htriData x hxbox htri
    exact bst_deg_ge_three_of_boxOpenForest hπ hxbox htri hvx hreach hcut
  have hvxinjOn : Set.InjOn vx Tf := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx hy
    have hx' : (vx x : Site d) = x := (htriData x hx.1 hx.2).1
    have hy' : (vx y : Site d) = y := (htriData y hy.1 hy.2).1
    rw [← hx', ← hy', hxy]
  set Tw : Finset (↑Vset : Type) := Tf.image vx with hTw
  have hcardTw : Tw.card = Tf.card := by rw [hTw, Finset.card_image_of_injOn hvxinjOn]
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ F.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨x, hxT, rfl⟩ := hw
    rw [tfc_mem_trifFinset] at hxT
    exact hdeg3 x hxT.1 hxT.2
  have h1 : Tf.card ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := by
    rw [← hcardTw]; exact flc2_trifImage_card_le_deg3 F Tw hTwdeg
  have h2 : (univ.filter (fun v => 3 ≤ F.degree v)).card
      ≤ (univ.filter (fun v => F.degree v = 1)).card :=
    flc2_forest_internal_le_leaves F hacyc hmin
  have h3 : (univ.filter (fun v => F.degree v = 1)).card ≤ boxSV_boundaryCard d (n + 1) := by
    rw [← tfc_boundaryFinset_card]
    apply Finset.card_le_card_of_injOn (fun v : (↑Vset : Type) => (v : Site d))
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, tfc_mem_boundaryFinset]
      exact hleaf v hv.2
    · intro u _ v _ huv; exact Subtype.val_injective huv
  calc Tcount d ω n = Tf.card := (tfc_trifFinset_card ω n).symm
    _ ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := h1
    _ ≤ (univ.filter (fun v => F.degree v = 1)).card := h2
    _ ≤ boxSV_boundaryCard d (n + 1) := h3


end StatMech.Percolation
